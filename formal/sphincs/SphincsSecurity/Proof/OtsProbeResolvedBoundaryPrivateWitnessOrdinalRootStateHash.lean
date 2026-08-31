import SphincsSecurity.Proof.OtsProbeResolvedBoundaryPrivateWitnessOrdinalRootStateSigner

/-!
# Safe direct hash queries under swapped roots

Structural input reconstruction may return different byte strings when one payload slot is the
hidden swapped root. The two runs nevertheless agree on whether every required value is present.
-/

namespace SphincsSecurity.Concrete.OtsProbeSimulation

open OracleComp OracleSpec
open OracleComp.ProgramLogic.Relational

def OptionShapeRel : Option α → Option β → Prop
  | none, none => True
  | some _, some _ => True
  | _, _ => False

def RootHiddenCleanRelWith
    (target : Position) (leftOutput rightOutput : HashOutput)
    (valueRel : α → β → Prop) :
    Option (CleanRunResult (α × SplitHashCache)) →
      Option (CleanRunResult (β × SplitHashCache)) → Prop
  | some left, some right =>
      RootHiddenStateRel target leftOutput rightOutput left.state right.state ∧
        left.remaining = right.remaining ∧ left.table = right.table ∧
        valueRel left.value.1 right.value.1 ∧
        RootHiddenCacheRel target leftOutput rightOutput left.value.2 right.value.2
  | none, none => True
  | _, _ => False

def RootHiddenRelatesWith
    (target : Position) (leftOutput rightOutput : HashOutput)
    (valueRel : α → β → Prop)
    (left : StateT SplitHashCache
      (OracleComp (LazyRevealProbe.World Coordinate)) α)
    (right : StateT SplitHashCache
      (OracleComp (LazyRevealProbe.World Coordinate)) β) : Prop :=
  ∀ leftState rightState,
    RootHiddenStateRel target leftOutput rightOutput leftState rightState →
    ∀ fuel table leftCache rightCache,
      RootHiddenCacheRel target leftOutput rightOutput leftCache rightCache →
      RelTriple
        (runCleanFromTable leftState fuel table (left.run leftCache))
        (runCleanFromTable rightState fuel table (right.run rightCache))
        (RootHiddenCleanRelWith target leftOutput rightOutput valueRel)

theorem rootHiddenRelatesWith_pure
    (target : Position) (leftOutput rightOutput : HashOutput)
    (leftValue : α) (rightValue : β) (hvalue : R leftValue rightValue) :
    RootHiddenRelatesWith target leftOutput rightOutput R
      (pure leftValue) (pure rightValue) := by
  intro leftState rightState hstate fuel table leftCache rightCache hcache
  simp only [StateT.run_pure, runCleanFromTable, OracleComp.construct_pure]
  exact relTriple_pure_pure ⟨hstate, rfl, rfl, hvalue, hcache⟩

theorem rootHiddenRelatesWith_pure_optionShape
    (target : Position) (leftOutput rightOutput : HashOutput)
    (leftValue : Option α) (rightValue : Option β)
    (hvalue : OptionShapeRel leftValue rightValue) :
    RootHiddenRelatesWith target leftOutput rightOutput OptionShapeRel
      (pure leftValue) (pure rightValue) :=
  rootHiddenRelatesWith_pure target leftOutput rightOutput leftValue rightValue hvalue

theorem RootHiddenRelatesWith.bind
    {target : Position} {leftOutput rightOutput : HashOutput}
    {left : StateT SplitHashCache
      (OracleComp (LazyRevealProbe.World Coordinate)) α}
    {right : StateT SplitHashCache
      (OracleComp (LazyRevealProbe.World Coordinate)) β}
    {leftNext : α → StateT SplitHashCache
      (OracleComp (LazyRevealProbe.World Coordinate)) γ}
    {rightNext : β → StateT SplitHashCache
      (OracleComp (LazyRevealProbe.World Coordinate)) δ}
    (hfirst : RootHiddenRelatesWith target leftOutput rightOutput R left right)
    (hnext : ∀ leftValue rightValue, R leftValue rightValue →
      RootHiddenRelatesWith target leftOutput rightOutput S
        (leftNext leftValue) (rightNext rightValue)) :
    RootHiddenRelatesWith target leftOutput rightOutput S
      (left >>= leftNext) (right >>= rightNext) := by
  intro leftState rightState hstate fuel table leftCache rightCache hcache
  rw [StateT.run_bind, StateT.run_bind, runCleanFromTable_bind,
    runCleanFromTable_bind]
  apply relTriple_bind
    (hfirst leftState rightState hstate fuel table leftCache rightCache hcache)
  intro leftResult rightResult hresult
  cases leftResult with
  | none =>
      cases rightResult with
      | none => exact relTriple_pure_pure trivial
      | some rightResult => simp [RootHiddenCleanRelWith] at hresult
  | some leftResult =>
      cases rightResult with
      | none => simp [RootHiddenCleanRelWith] at hresult
      | some rightResult =>
          rcases hresult with ⟨hnextState, hremaining, htable, hvalue, hnextCache⟩
          simp only
          rw [← hremaining, ← htable]
          exact hnext leftResult.value.1 rightResult.value.1 hvalue
            leftResult.state rightResult.state hnextState leftResult.remaining leftResult.table
              leftResult.value.2 rightResult.value.2 hnextCache

theorem rootHiddenRelatesWith_peekCoordinate
    (target : Position) (leftOutput rightOutput : HashOutput)
    (coordinate : Coordinate) :
    RootHiddenRelatesWith target leftOutput rightOutput OptionShapeRel
      (peekCoordinate coordinate) (peekCoordinate coordinate) := by
  intro leftState rightState hstate fuel table leftCache rightCache hcache
  rw [peekCoordinate_run_eq, peekCoordinate_run_eq, LazyRevealProbe.peekQuery,
    runCleanFromTable_peek_query_bind, runCleanFromTable_peek_query_bind]
  simp only [runCleanFromTable, OracleComp.construct_pure]
  refine relTriple_pure_pure ⟨hstate, rfl, rfl, ?_, hcache⟩
  have hpresent := hstate.values_isSome_eq coordinate
  cases hleft : leftState.values coordinate <;>
    cases hright : rightState.values coordinate <;>
      simp [hleft, hright, OptionShapeRel] at hpresent ⊢

theorem rootHiddenRelatesWith_peekPositionValues
    (target : Position) (leftOutput rightOutput : HashOutput) : ∀ positions,
    RootHiddenRelatesWith target leftOutput rightOutput OptionShapeRel
      (peekPositionValues positions) (peekPositionValues positions)
  | [] => by
      simp only [peekPositionValues]
      exact rootHiddenRelatesWith_pure_optionShape target leftOutput rightOutput
        (some []) (some []) trivial
  | position :: remaining => by
      simp only [peekPositionValues]
      apply (rootHiddenRelatesWith_peekCoordinate target leftOutput rightOutput
        (.position position)).bind
      intro leftValue rightValue hvalue
      cases leftValue with
      | none =>
          cases rightValue with
          | none =>
              simp only
              exact rootHiddenRelatesWith_pure_optionShape target leftOutput rightOutput none none
                trivial
          | some rightValue => simp [OptionShapeRel] at hvalue
      | some leftValue =>
          cases rightValue with
          | none => simp [OptionShapeRel] at hvalue
          | some rightValue =>
              apply (rootHiddenRelatesWith_peekPositionValues target leftOutput rightOutput
                remaining).bind
              intro leftTail rightTail htail
              cases leftTail with
              | none =>
                  cases rightTail with
                  | none =>
                      simp only
                      exact rootHiddenRelatesWith_pure_optionShape target leftOutput rightOutput
                        none none
                        trivial
                  | some rightTail => simp [OptionShapeRel] at htail
              | some leftTail =>
                  cases rightTail with
                  | none => simp [OptionShapeRel] at htail
                  | some rightTail =>
                      simp only
                      exact rootHiddenRelatesWith_pure_optionShape target leftOutput rightOutput
                        (some (leftValue :: leftTail)) (some (rightValue :: rightTail)) trivial

theorem rootHiddenRelatesWith_peekTableInput
    (parameter : PublicParameter)
    (target : Position) (leftOutput rightOutput : HashOutput)
    (coordinate : Coordinate) :
    RootHiddenRelatesWith target leftOutput rightOutput OptionShapeRel
      (peekTableInput parameter coordinate) (peekTableInput parameter coordinate) := by
  cases coordinate with
  | chainStart =>
      exact rootHiddenRelatesWith_pure_optionShape target leftOutput rightOutput none none trivial
  | position position =>
      cases position with
      | chain lay tree leafIdx chainIdx step =>
          rw [peekTableInput.eq_2]
          by_cases hzero : step.val = 0
          · rw [if_pos hzero]
            apply (rootHiddenRelatesWith_peekCoordinate target leftOutput rightOutput
              (.chainStart lay tree leafIdx chainIdx)).bind
            intro leftValue rightValue hvalue
            cases leftValue with
            | none =>
                cases rightValue with
                | none =>
                    simp only
                    exact rootHiddenRelatesWith_pure_optionShape target leftOutput rightOutput
                      none none trivial
                | some rightValue => simp [OptionShapeRel] at hvalue
            | some leftValue =>
                cases rightValue with
                | none => simp [OptionShapeRel] at hvalue
                | some rightValue =>
                    simp only
                    exact rootHiddenRelatesWith_pure_optionShape target leftOutput rightOutput _ _
                      trivial
          · rw [if_neg hzero]
            change RootHiddenRelatesWith target leftOutput rightOutput OptionShapeRel
              (peekPositionValues (Position.chain lay tree leafIdx chainIdx step).children >>=
                fun values => match values with
                  | none => pure none
                  | some values => pure (some (tweakableHashInput parameter
                      (Position.chain lay tree leafIdx chainIdx step).domain
                      (values.flatMap digestBytes))))
              (peekPositionValues (Position.chain lay tree leafIdx chainIdx step).children >>=
                fun values => match values with
                  | none => pure none
                  | some values => pure (some (tweakableHashInput parameter
                      (Position.chain lay tree leafIdx chainIdx step).domain
                      (values.flatMap digestBytes))))
            apply (rootHiddenRelatesWith_peekPositionValues target leftOutput rightOutput
              (Position.chain lay tree leafIdx chainIdx step).children).bind
            intro leftValues rightValues hvalues
            cases leftValues with
            | none =>
                cases rightValues with
                | none =>
                    simp only
                    exact rootHiddenRelatesWith_pure_optionShape target leftOutput rightOutput
                      none none trivial
                | some rightValues => simp [OptionShapeRel] at hvalues
            | some leftValues =>
                cases rightValues with
                | none => simp [OptionShapeRel] at hvalues
                | some rightValues =>
                    simp only
                    exact rootHiddenRelatesWith_pure_optionShape target leftOutput rightOutput _ _
                      trivial
      | leaf | node | ftsLeaf | ftsNode | ftsRoots =>
          simp only [peekTableInput]
          apply (rootHiddenRelatesWith_peekPositionValues target leftOutput rightOutput _).bind
          intro leftValues rightValues hvalues
          cases leftValues with
          | none =>
              cases rightValues with
              | none =>
                  simp only
                  exact rootHiddenRelatesWith_pure_optionShape target leftOutput rightOutput
                    none none trivial
              | some rightValues => simp [OptionShapeRel] at hvalues
          | some leftValues =>
              cases rightValues with
              | none => simp [OptionShapeRel] at hvalues
              | some rightValues =>
                  simp only
                  exact rootHiddenRelatesWith_pure_optionShape target leftOutput rightOutput _ _
                    trivial

theorem relTriple_rootHidden_resolveKnownInput_of_miss
    (parameter : PublicParameter)
    (target : Position) (leftOutput rightOutput : HashOutput)
    (coordinate : Coordinate) (input : HashInput)
    (leftState rightState : LazyRevealProbe.State Coordinate)
    (hstate : RootHiddenStateRel target leftOutput rightOutput leftState rightState)
    (fuel : Nat) (table : OtsSecretIndex → HashOutput)
    (leftCache rightCache : SplitHashCache)
    (hcache : RootHiddenCacheRel target leftOutput rightOutput leftCache rightCache)
    (hleftMiss : ∀ result,
      some result ∈ support (runCleanFromTable leftState fuel table
        ((peekTableInput parameter coordinate).run leftCache)) →
      result.value.1 ≠ some input)
    (hrightMiss : ∀ result,
      some result ∈ support (runCleanFromTable rightState fuel table
        ((peekTableInput parameter coordinate).run rightCache)) →
      result.value.1 ≠ some input) :
    RelTriple
      (runCleanFromTable leftState fuel table
        ((resolveKnownInput parameter coordinate input).run leftCache))
      (runCleanFromTable rightState fuel table
        ((resolveKnownInput parameter coordinate input).run rightCache))
      (RootHiddenCleanSameRel target leftOutput rightOutput) := by
  unfold resolveKnownInput
  rw [StateT.run_bind, StateT.run_bind, runCleanFromTable_bind,
    runCleanFromTable_bind]
  let leftRun := runCleanFromTable leftState fuel table
    ((peekTableInput parameter coordinate).run leftCache)
  let rightRun := runCleanFromTable rightState fuel table
    ((peekTableInput parameter coordinate).run rightCache)
  have hpeek := rootHiddenRelatesWith_peekTableInput parameter target leftOutput rightOutput
    coordinate leftState rightState hstate fuel table leftCache rightCache hcache
  have hleftSupport :=
    SphincsSecurity.Concrete.FtsProbeSimulation.relTriple_and_left_support hpeek
      (fun result => result ∈ support leftRun) (fun result hresult => hresult)
  have hbothSupport :=
    SphincsSecurity.Concrete.FtsProbeSimulation.relTriple_and_right_support hleftSupport
  apply relTriple_bind hbothSupport
  intro leftResult rightResult hresult
  rcases hresult with ⟨⟨hrelation, hleftMem⟩, hrightMem⟩
  cases leftResult with
  | none =>
      cases rightResult with
      | none => exact relTriple_pure_pure trivial
      | some rightResult => simp [RootHiddenCleanRelWith] at hrelation
  | some leftResult =>
      cases rightResult with
      | none => simp [RootHiddenCleanRelWith] at hrelation
      | some rightResult =>
          rcases hrelation with ⟨hnextState, hremaining, htable, hshape, hnextCache⟩
          simp only
          rw [← hremaining, ← htable]
          cases hleftKnown : leftResult.value.1 with
          | none =>
              cases hrightKnown : rightResult.value.1 with
              | none =>
                  exact rootHiddenRelates_splitHashQuery_ordinary target leftOutput rightOutput
                    input leftResult.state rightResult.state hnextState leftResult.remaining
                      leftResult.table leftResult.value.2 rightResult.value.2 hnextCache
              | some rightKnown =>
                  simp [hleftKnown, hrightKnown, OptionShapeRel] at hshape
          | some leftKnown =>
              cases hrightKnown : rightResult.value.1 with
              | none => simp [hleftKnown, hrightKnown, OptionShapeRel] at hshape
              | some rightKnown =>
                  have hleftNe : leftKnown ≠ input := by
                    intro heq
                    apply hleftMiss leftResult hleftMem
                    rw [hleftKnown, heq]
                  have hrightNe : rightKnown ≠ input := by
                    intro heq
                    apply hrightMiss rightResult hrightMem
                    rw [hrightKnown, heq]
                  simp only
                  rw [if_neg hleftNe, if_neg hrightNe]
                  exact rootHiddenRelates_splitHashQuery_ordinary target leftOutput rightOutput
                    input leftResult.state rightResult.state hnextState leftResult.remaining
                      leftResult.table leftResult.value.2 rightResult.value.2 hnextCache

end SphincsSecurity.Concrete.OtsProbeSimulation
