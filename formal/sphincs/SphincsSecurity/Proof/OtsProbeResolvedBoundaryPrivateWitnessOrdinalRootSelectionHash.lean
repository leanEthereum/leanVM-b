import SphincsSecurity.Proof.OtsProbeResolvedBoundaryPrivateWitnessOrdinalRootSelectionEncoding

/-!
# Hidden-root planned hash coupling

When the selected root is not one of a structural input's children, both materialized states
reconstruct exactly the same input. This module gives the exact lookup and resolver coupling for
that branch. The complementary child branch is handled by the recorded candidate miss.
-/

namespace SphincsSecurity.Concrete.OtsProbeSimulation

open OracleComp OracleSpec
open OracleComp.ProgramLogic.Relational

theorem rootHiddenRelates_of_with_eq
    (target : Position) (leftOutput rightOutput : HashOutput)
    (left right : StateT SplitHashCache
      (OracleComp (LazyRevealProbe.World Coordinate)) α)
    (hrel : RootHiddenRelatesWith target leftOutput rightOutput (· = ·) left right) :
    RootHiddenRelates target leftOutput rightOutput left right := by
  intro leftState rightState hstate fuel table leftCache rightCache hcache
  apply relTriple_post_mono
    (hrel leftState rightState hstate fuel table leftCache rightCache hcache)
  intro leftResult rightResult hresult
  cases leftResult with
  | none =>
      cases rightResult with
      | none => trivial
      | some rightResult => exact False.elim hresult
  | some leftResult =>
      cases rightResult with
      | none => exact False.elim hresult
      | some rightResult =>
          change RootHiddenStateRel target leftOutput rightOutput
              leftResult.state rightResult.state ∧
            leftResult.remaining = rightResult.remaining ∧
            leftResult.table = rightResult.table ∧
            leftResult.value.1 = rightResult.value.1 ∧
            RootHiddenCacheRel target leftOutput rightOutput
              leftResult.value.2 rightResult.value.2 at hresult ⊢
          exact hresult

theorem rootHiddenRelatesWith_peekCoordinate_eq_of_ne
    (target : Position) (leftOutput rightOutput : HashOutput)
    (coordinate : Coordinate) (hne : coordinate ≠ .position target) :
    RootHiddenRelatesWith target leftOutput rightOutput (· = ·)
      (peekCoordinate coordinate) (peekCoordinate coordinate) := by
  intro leftState rightState hstate fuel table leftCache rightCache hcache
  rw [peekCoordinate_run_eq, peekCoordinate_run_eq, LazyRevealProbe.peekQuery,
    runCleanFromTable_peek_query_bind, runCleanFromTable_peek_query_bind]
  simp only [runCleanFromTable, OracleComp.construct_pure]
  exact relTriple_pure_pure
    ⟨hstate, rfl, rfl,
      congrArg (Option.map truncateHash) (hstate.other_values coordinate hne), hcache⟩

theorem rootHiddenRelatesWith_peekPositionValues_eq_of_not_mem
    (target : Position) (leftOutput rightOutput : HashOutput) : ∀ positions,
    target ∉ positions →
    RootHiddenRelatesWith target leftOutput rightOutput (· = ·)
      (peekPositionValues positions) (peekPositionValues positions)
  | [], _ => by
      simp only [peekPositionValues]
      exact rootHiddenRelatesWith_pure target leftOutput rightOutput
        (some ([] : List Digest)) (some []) rfl
  | position :: remaining, hnot => by
      simp only [peekPositionValues]
      have hposition : position ≠ target := by
        intro heq
        apply hnot
        simp [heq]
      have hremaining : target ∉ remaining := by
        intro hmem
        exact hnot (List.mem_cons_of_mem position hmem)
      apply (rootHiddenRelatesWith_peekCoordinate_eq_of_ne target leftOutput rightOutput
        (.position position) (by simpa using hposition)).bind
      intro leftValue rightValue hvalue
      subst rightValue
      cases leftValue with
      | none =>
          exact rootHiddenRelatesWith_pure target leftOutput rightOutput
            (none : Option (List Digest)) none rfl
      | some value =>
          apply (rootHiddenRelatesWith_peekPositionValues_eq_of_not_mem target leftOutput
            rightOutput remaining hremaining).bind
          intro leftTail rightTail htail
          subst rightTail
          cases leftTail with
          | none =>
              exact rootHiddenRelatesWith_pure target leftOutput rightOutput
                (none : Option (List Digest)) none rfl
          | some tail =>
              exact rootHiddenRelatesWith_pure target leftOutput rightOutput
                (some (value :: tail)) (some (value :: tail)) rfl

theorem rootHiddenRelatesWith_peekTableInput_position_eq_of_not_mem_children
    (parameter : PublicParameter)
    (target : Position) (leftOutput rightOutput : HashOutput)
    (position : Position) (hnot : target ∉ position.children) :
    RootHiddenRelatesWith target leftOutput rightOutput (· = ·)
      (peekTableInput parameter (.position position))
      (peekTableInput parameter (.position position)) := by
  cases position with
  | chain lay tree leafIdx chainIdx step =>
      rw [peekTableInput.eq_2]
      by_cases hzero : step.val = 0
      · rw [if_pos hzero]
        apply (rootHiddenRelatesWith_peekCoordinate_eq_of_ne target leftOutput rightOutput
          (.chainStart lay tree leafIdx chainIdx) (by simp)).bind
        intro leftValue rightValue hvalue
        subst rightValue
        cases leftValue with
        | none =>
            exact rootHiddenRelatesWith_pure target leftOutput rightOutput
              (none : Option HashInput) none rfl
        | some value =>
            exact rootHiddenRelatesWith_pure target leftOutput rightOutput
              (some _) (some _) rfl
      · rw [if_neg hzero]
        apply (rootHiddenRelatesWith_peekPositionValues_eq_of_not_mem target leftOutput
          rightOutput _ hnot).bind
        intro leftValues rightValues hvalues
        subst rightValues
        cases leftValues with
        | none =>
            exact rootHiddenRelatesWith_pure target leftOutput rightOutput
              (none : Option HashInput) none rfl
        | some values =>
            exact rootHiddenRelatesWith_pure target leftOutput rightOutput
              (some _) (some _) rfl
  | leaf lay tree leafIdx =>
      simp only [peekTableInput]
      apply (rootHiddenRelatesWith_peekPositionValues_eq_of_not_mem target leftOutput
        rightOutput _ hnot).bind
      intro leftValues rightValues hvalues
      subst rightValues
      cases leftValues with
      | none =>
          exact rootHiddenRelatesWith_pure target leftOutput rightOutput
            (none : Option HashInput) none rfl
      | some values =>
          exact rootHiddenRelatesWith_pure target leftOutput rightOutput
            (some _) (some _) rfl
  | node lay tree level nodeIdx =>
      simp only [peekTableInput]
      apply (rootHiddenRelatesWith_peekPositionValues_eq_of_not_mem target leftOutput
        rightOutput _ hnot).bind
      intro leftValues rightValues hvalues
      subst rightValues
      cases leftValues with
      | none =>
          exact rootHiddenRelatesWith_pure target leftOutput rightOutput
            (none : Option HashInput) none rfl
      | some values =>
          exact rootHiddenRelatesWith_pure target leftOutput rightOutput
            (some _) (some _) rfl
  | ftsLeaf index tree leafIdx =>
      simp only [peekTableInput]
      apply (rootHiddenRelatesWith_peekPositionValues_eq_of_not_mem target leftOutput
        rightOutput _ hnot).bind
      intro leftValues rightValues hvalues
      subst rightValues
      cases leftValues with
      | none =>
          exact rootHiddenRelatesWith_pure target leftOutput rightOutput
            (none : Option HashInput) none rfl
      | some values =>
          exact rootHiddenRelatesWith_pure target leftOutput rightOutput
            (some _) (some _) rfl
  | ftsNode index tree level nodeIdx =>
      simp only [peekTableInput]
      apply (rootHiddenRelatesWith_peekPositionValues_eq_of_not_mem target leftOutput
        rightOutput _ hnot).bind
      intro leftValues rightValues hvalues
      subst rightValues
      cases leftValues with
      | none =>
          exact rootHiddenRelatesWith_pure target leftOutput rightOutput
            (none : Option HashInput) none rfl
      | some values =>
          exact rootHiddenRelatesWith_pure target leftOutput rightOutput
            (some _) (some _) rfl
  | ftsRoots index =>
      simp only [peekTableInput]
      apply (rootHiddenRelatesWith_peekPositionValues_eq_of_not_mem target leftOutput
        rightOutput _ hnot).bind
      intro leftValues rightValues hvalues
      subst rightValues
      cases leftValues with
      | none =>
          exact rootHiddenRelatesWith_pure target leftOutput rightOutput
            (none : Option HashInput) none rfl
      | some values =>
          exact rootHiddenRelatesWith_pure target leftOutput rightOutput
            (some _) (some _) rfl

theorem rootHiddenRelates_modify_ordinary_pure
    (target : Position) (leftOutput rightOutput : HashOutput)
    (input : HashInput) (output : HashOutput) :
    RootHiddenRelates target leftOutput rightOutput
      ((do
        modify (fun cache : SplitHashCache =>
          Function.update cache (.ordinary input) (some output))
        pure output) : StateT SplitHashCache
          (OracleComp (LazyRevealProbe.World Coordinate)) HashOutput)
      ((do
        modify (fun cache : SplitHashCache =>
          Function.update cache (.ordinary input) (some output))
        pure output) : StateT SplitHashCache
          (OracleComp (LazyRevealProbe.World Coordinate)) HashOutput) := by
  intro leftState rightState hstate fuel table leftCache rightCache hcache
  simp only [StateT.run_bind, StateT.run_modify, StateT.run_pure, runCleanFromTable]
  exact relTriple_pure_pure
    ⟨hstate, rfl, rfl, rfl, hcache.update_same_ordinary input output⟩

theorem rootHiddenRelates_revealCoordinateOutput_of_ne
    (target : Position) (leftOutput rightOutput : HashOutput)
    (coordinate : Coordinate) (hne : coordinate ≠ .position target) :
    RootHiddenRelates target leftOutput rightOutput
      (revealCoordinateOutput coordinate) (revealCoordinateOutput coordinate) := by
  intro leftState rightState hstate fuel table leftCache rightCache hcache
  rw [revealCoordinateOutput_run_eq, revealCoordinateOutput_run_eq,
    LazyRevealProbe.revealQuery, runCleanFromTable_reveal_query_bind,
    runCleanFromTable_reveal_query_bind]
  have hvalue := hstate.other_values coordinate hne
  cases hleft : leftState.values coordinate with
  | some output =>
      have hright : rightState.values coordinate = some output := by
        rw [← hvalue]
        exact hleft
      simp only [hright, runCleanFromTable, OracleComp.construct_pure]
      exact relTriple_pure_pure ⟨hstate, rfl, rfl, rfl,
        hcache.update_same_hidden_of_ne coordinate output hne⟩
  | none =>
      have hright : rightState.values coordinate = none := by
        rw [← hvalue]
        exact hleft
      simp only [hright]
      cases coordinate with
      | chainStart lay tree leafIdx chainIdx =>
          simp only
          let output := table ⟨lay, tree, leafIdx, chainIdx⟩
          have hhit := hstate.hitAt_eq (.chainStart lay tree leafIdx chainIdx) output
          by_cases hleftHit : leftState.hitAt (.chainStart lay tree leafIdx chainIdx) output
          · have hrightHit := hhit.mp hleftHit
            change leftState.hitAt (.chainStart lay tree leafIdx chainIdx)
              (table ⟨lay, tree, leafIdx, chainIdx⟩) at hleftHit
            change rightState.hitAt (.chainStart lay tree leafIdx chainIdx)
              (table ⟨lay, tree, leafIdx, chainIdx⟩) at hrightHit
            rw [if_pos hleftHit, if_pos hrightHit]
            exact relTriple_pure_pure trivial
          · have hrightHit : ¬rightState.hitAt
                (.chainStart lay tree leafIdx chainIdx) output :=
              fun h => hleftHit (hhit.mpr h)
            simp only [output, hleftHit, hrightHit, ↓reduceIte,
              runCleanFromTable, OracleComp.construct_pure]
            exact relTriple_pure_pure ⟨hstate.materialize_other
                (.chainStart lay tree leafIdx chainIdx) output hne,
              rfl, rfl, rfl,
              hcache.update_same_hidden_of_ne
                (.chainStart lay tree leafIdx chainIdx) output hne⟩
      | position position =>
          apply relTriple_bind (relTriple_refl LazyRevealProbe.sampleHashOutput)
          intro leftSample rightSample hsample
          subst rightSample
          have hhit := hstate.hitAt_eq (.position position) leftSample
          by_cases hleftHit : leftState.hitAt (.position position) leftSample
          · have hrightHit := hhit.mp hleftHit
            simp [hleftHit, hrightHit, RootHiddenCleanSameRel]
          · have hrightHit : ¬rightState.hitAt (.position position) leftSample :=
              fun h => hleftHit (hhit.mpr h)
            simp only [hleftHit, hrightHit, ↓reduceIte,
              runCleanFromTable, OracleComp.construct_pure]
            exact relTriple_pure_pure ⟨hstate.materialize_other
                (.position position) leftSample hne,
              rfl, rfl, rfl,
              hcache.update_same_hidden_of_ne (.position position) leftSample hne⟩

set_option maxHeartbeats 2000000 in
set_option maxRecDepth 100000 in
theorem rootHiddenRelates_resolveKnownInput_of_not_mem_children
    (parameter : PublicParameter)
    (target : Position) (leftOutput rightOutput : HashOutput)
    (position : Position) (hposition : position ≠ target)
    (hnot : target ∉ position.children) (input : HashInput) :
    RootHiddenRelates target leftOutput rightOutput
      (resolveKnownInput parameter (.position position) input)
      (resolveKnownInput parameter (.position position) input) := by
  unfold resolveKnownInput
  apply (rootHiddenRelates_of_with_eq target leftOutput rightOutput _ _
    (rootHiddenRelatesWith_peekTableInput_position_eq_of_not_mem_children parameter target
      leftOutput rightOutput position hnot)).bind
  intro leftKnown rightKnown hknown
  subst rightKnown
  cases leftKnown with
  | none =>
      exact rootHiddenRelates_splitHashQuery_ordinary target leftOutput rightOutput input
  | some knownInput =>
      by_cases heq : knownInput = input
      · simp only [heq, ↓reduceIte]
        apply (rootHiddenRelates_revealCoordinateOutput_of_ne target leftOutput rightOutput
          (.position position) (by simpa using hposition)).bind
        intro leftValue rightValue hvalue
        subst rightValue
        apply (rootHiddenRelates_publishCoordinate_of_ne target leftOutput rightOutput
          (.position position) (by simpa using hposition)).bind
        intro _ _ _
        exact rootHiddenRelates_modify_ordinary_pure target leftOutput rightOutput input leftValue
      · simp only [heq, ↓reduceIte]
        exact rootHiddenRelates_splitHashQuery_ordinary target leftOutput rightOutput input

theorem rootHiddenRelates_executeCandidate
    (target : Position) (leftOutput rightOutput : HashOutput)
    (candidate? : Option Probe) :
    RootHiddenRelates target leftOutput rightOutput
      (executeCandidate? candidate?) (executeCandidate? candidate?) := by
  cases candidate? with
  | none => exact rootHiddenRelates_pure target leftOutput rightOutput ()
  | some candidate => exact rootHiddenRelates_probe target leftOutput rightOutput candidate

theorem rootHiddenRelates_resolvePublicKnownInput_of_ne
    (parameter : PublicParameter)
    (target : Position) (leftOutput rightOutput : HashOutput)
    (publicState : LazyRevealProbe.State Coordinate)
    (coordinate : Coordinate) (hne : coordinate ≠ .position target)
    (input : HashInput) :
    RootHiddenRelates target leftOutput rightOutput
      (resolvePublicKnownInput parameter publicState coordinate input)
      (resolvePublicKnownInput parameter publicState coordinate input) := by
  unfold resolvePublicKnownInput
  cases hknown : purePeekTableInput parameter publicState coordinate with
  | none =>
      exact rootHiddenRelates_splitHashQuery_ordinary target leftOutput rightOutput input
  | some knownInput =>
      by_cases heq : knownInput = input
      · simp only [heq, ↓reduceIte]
        apply (rootHiddenRelates_revealCoordinateOutput_of_ne target leftOutput rightOutput
          coordinate hne).bind
        intro leftValue rightValue hvalue
        subst rightValue
        apply (rootHiddenRelates_publishCoordinate_of_ne target leftOutput rightOutput
          coordinate hne).bind
        intro _ _ _
        exact rootHiddenRelates_modify_ordinary_pure target leftOutput rightOutput input leftValue
      · simp only [heq, ↓reduceIte]
        exact rootHiddenRelates_splitHashQuery_ordinary target leftOutput rightOutput input

theorem rootHiddenRelates_probingHashQueryAfterPublicPlan
    (parameter : PublicParameter)
    (target : Position) (leftOutput rightOutput : HashOutput)
    (input : HashInput) (publicState : LazyRevealProbe.State Coordinate)
    (plan : PlannedHashQuery)
    (hsafe : plan.action ≠ .resolve (.position target)) :
    RootHiddenRelates target leftOutput rightOutput
      (probingHashQueryAfterPublicPlan parameter input publicState plan)
      (probingHashQueryAfterPublicPlan parameter input publicState plan) := by
  unfold probingHashQueryAfterPublicPlan
  apply (rootHiddenRelates_executeCandidate target leftOutput rightOutput plan.candidate?).bind
  intro _ _ _
  cases haction : plan.action with
  | ordinary =>
      exact rootHiddenRelates_splitHashQuery_ordinary target leftOutput rightOutput input
  | resolve coordinate =>
      have hne : coordinate ≠ .position target := by
        intro heq
        apply hsafe
        rw [haction, heq]
      exact rootHiddenRelates_resolvePublicKnownInput_of_ne parameter target leftOutput
        rightOutput publicState coordinate hne input

end SphincsSecurity.Concrete.OtsProbeSimulation
