import SphincsSecurity.Proof.OtsProbeResolvedBoundaryPrivateWitnessOrdinalRootGlobalSourceDelayedRootBridge

/-!
# Delayed selector root swap

The delayed selector must retain executions that encounter an unrelated pending hit. Its root
exchange therefore runs in the permissive interpreter itself, rather than passing through the
failure-discarding materialized selector.
-/

namespace SphincsSecurity.Concrete.OtsProbeSimulation

open OracleComp OracleSpec
open OracleComp.ProgramLogic.Relational

def RootHiddenPermissiveRelatesWith
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
        (runPermissiveFromTable leftState fuel table (left.run leftCache))
        (runPermissiveFromTable rightState fuel table (right.run rightCache))
        (RootHiddenCleanRelWith target leftOutput rightOutput valueRel)

theorem rootHiddenPermissiveRelatesWith_pure
    (target : Position) (leftOutput rightOutput : HashOutput)
    (leftValue : α) (rightValue : β) (hvalue : R leftValue rightValue) :
    RootHiddenPermissiveRelatesWith target leftOutput rightOutput R
      (pure leftValue) (pure rightValue) := by
  intro leftState rightState hstate fuel table leftCache rightCache hcache
  simp only [StateT.run_pure, runPermissiveFromTable, OracleComp.construct_pure]
  exact relTriple_pure_pure ⟨hstate, rfl, rfl, hvalue, hcache⟩

theorem RootHiddenPermissiveRelatesWith.bind
    {target : Position} {leftOutput rightOutput : HashOutput}
    {left : StateT SplitHashCache
      (OracleComp (LazyRevealProbe.World Coordinate)) α}
    {right : StateT SplitHashCache
      (OracleComp (LazyRevealProbe.World Coordinate)) β}
    {leftNext : α → StateT SplitHashCache
      (OracleComp (LazyRevealProbe.World Coordinate)) γ}
    {rightNext : β → StateT SplitHashCache
      (OracleComp (LazyRevealProbe.World Coordinate)) δ}
    (hfirst : RootHiddenPermissiveRelatesWith target leftOutput rightOutput R left right)
    (hnext : ∀ leftValue rightValue, R leftValue rightValue →
      RootHiddenPermissiveRelatesWith target leftOutput rightOutput S
        (leftNext leftValue) (rightNext rightValue)) :
    RootHiddenPermissiveRelatesWith target leftOutput rightOutput S
      (left >>= leftNext) (right >>= rightNext) := by
  intro leftState rightState hstate fuel table leftCache rightCache hcache
  rw [StateT.run_bind, StateT.run_bind, runPermissiveFromTable_bind,
    runPermissiveFromTable_bind]
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

def RootHiddenPermissiveRelates
    (target : Position) (leftOutput rightOutput : HashOutput)
    (left right : StateT SplitHashCache
      (OracleComp (LazyRevealProbe.World Coordinate)) α) : Prop :=
  RootHiddenPermissiveRelatesWith target leftOutput rightOutput (fun x y => x = y) left right

theorem rootHiddenPermissiveRelates_pure
    (target : Position) (leftOutput rightOutput : HashOutput) (value : α) :
    RootHiddenPermissiveRelates target leftOutput rightOutput (pure value) (pure value) :=
  rootHiddenPermissiveRelatesWith_pure target leftOutput rightOutput value value rfl

theorem rootHiddenPermissiveRelates_splitUniformImpl
    (target : Position) (leftOutput rightOutput : HashOutput) (n : Nat) :
    RootHiddenPermissiveRelates target leftOutput rightOutput
      (splitUniformImpl n) (splitUniformImpl n) := by
  intro leftState rightState hstate fuel table leftCache rightCache hcache
  unfold splitUniformImpl LazyRevealProbe.uniformQuery
  rw [StateT.run_liftM, StateT.run_liftM,
    runPermissiveFromTable_uniform_query_bind, runPermissiveFromTable_uniform_query_bind]
  apply relTriple_bind
    (relTriple_refl (liftM (unifSpec.query n) : ProbComp (Fin (n + 1))))
  intro leftValue rightValue hvalue
  subst rightValue
  simp only [runPermissiveFromTable, OracleComp.construct_pure]
  exact relTriple_pure_pure ⟨hstate, rfl, rfl, rfl, hcache⟩

theorem rootHiddenPermissiveRelates_ensureCoordinate
    (target : Position) (leftOutput rightOutput : HashOutput)
    (coordinate : Coordinate) :
    RootHiddenPermissiveRelates target leftOutput rightOutput
      (ensureCoordinate coordinate) (ensureCoordinate coordinate) := by
  intro leftState rightState hstate fuel table leftCache rightCache hcache
  unfold ensureCoordinate LazyRevealProbe.ensureQuery
  rw [StateT.run_liftM, StateT.run_liftM,
    runPermissiveFromTable_ensure_query_bind, runPermissiveFromTable_ensure_query_bind]
  simp only [runPermissiveFromTable, OracleComp.construct_pure]
  exact relTriple_pure_pure ⟨hstate.ensure coordinate, rfl, rfl, trivial, hcache⟩

theorem rootHiddenPermissiveRelates_probe
    (target : Position) (leftOutput rightOutput : HashOutput)
    (candidate : Probe) :
    RootHiddenPermissiveRelates target leftOutput rightOutput
      (probe candidate) (probe candidate) := by
  intro leftState rightState hstate fuel table leftCache rightCache hcache
  unfold probe LazyRevealProbe.probeQuery
  rw [StateT.run_liftM, StateT.run_liftM,
    runPermissiveFromTable_probe_query_bind, runPermissiveFromTable_probe_query_bind]
  cases fuel with
  | zero => exact relTriple_pure_pure trivial
  | succ remaining =>
      have hrevealed : candidate.coordinate ∈ leftState.revealed ↔
          candidate.coordinate ∈ rightState.revealed := by rw [hstate.revealed]
      by_cases hleftRevealed : candidate.coordinate ∈ leftState.revealed
      · have hrightRevealed := hrevealed.mp hleftRevealed
        simp only [hleftRevealed, hrightRevealed, ↓reduceIte,
          runPermissiveFromTable, OracleComp.construct_pure]
        exact relTriple_pure_pure ⟨hstate, rfl, rfl, trivial, hcache⟩
      · have hrightRevealed : candidate.coordinate ∉ rightState.revealed :=
          fun hmem => hleftRevealed (hrevealed.mpr hmem)
        simp only [hleftRevealed, hrightRevealed, ↓reduceIte,
          runPermissiveFromTable, OracleComp.construct_pure]
        exact relTriple_pure_pure
          ⟨hstate.addPending candidate.coordinate candidate.candidate,
            rfl, rfl, trivial, hcache⟩

theorem rootHiddenPermissiveRelates_splitHashQuery_ordinary
    (target : Position) (leftOutput rightOutput : HashOutput)
    (input : HashInput) :
    RootHiddenPermissiveRelates target leftOutput rightOutput
      (splitHashQuery (.ordinary input)) (splitHashQuery (.ordinary input)) := by
  intro leftState rightState hstate fuel table leftCache rightCache hcache
  have hlookup := hcache.ordinary input
  rw [splitHashQuery_run_eq, splitHashQuery_run_eq]
  cases hleft : leftCache (.ordinary input) with
  | some output =>
      have hright : rightCache (.ordinary input) = some output := by
        rw [← hlookup]
        exact hleft
      simp only [hright, runPermissiveFromTable, OracleComp.construct_pure]
      exact relTriple_pure_pure ⟨hstate, rfl, rfl, rfl, hcache⟩
  | none =>
      have hright : rightCache (.ordinary input) = none := by
        rw [← hlookup]
        exact hleft
      simp only [hright]
      unfold LazyRevealProbe.hashOutputQuery
      rw [runPermissiveFromTable_hashOutput_query_bind,
        runPermissiveFromTable_hashOutput_query_bind]
      apply relTriple_bind (relTriple_refl LazyRevealProbe.sampleHashOutput)
      intro leftSample rightSample hsample
      subst rightSample
      simp only [runPermissiveFromTable, OracleComp.construct_pure]
      exact relTriple_pure_pure ⟨hstate, rfl, rfl, rfl,
        hcache.update_same_ordinary input leftSample⟩

theorem rootHiddenPermissiveRelates_revealCoordinate_of_ne
    (target : Position) (leftOutput rightOutput : HashOutput)
    (coordinate : Coordinate) (hne : coordinate ≠ .position target) :
    RootHiddenPermissiveRelates target leftOutput rightOutput
      (revealCoordinate coordinate) (revealCoordinate coordinate) := by
  intro leftState rightState hstate fuel table leftCache rightCache hcache
  rw [revealCoordinate_run, revealCoordinate_run, LazyRevealProbe.revealQuery,
    runPermissiveFromTable_reveal_query_bind, runPermissiveFromTable_reveal_query_bind]
  have hvalue := hstate.other_values coordinate hne
  cases hleft : leftState.values coordinate with
  | some output =>
      have hright : rightState.values coordinate = some output := by
        rw [← hvalue]
        exact hleft
      simp only [hright, runPermissiveFromTable, OracleComp.construct_pure]
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
          simp only [runPermissiveFromTable, OracleComp.construct_pure]
          exact relTriple_pure_pure
            ⟨hstate.materialize_other (.chainStart lay tree leafIdx chainIdx) output hne,
              rfl, rfl, rfl,
              hcache.update_same_hidden_of_ne
                (.chainStart lay tree leafIdx chainIdx) output hne⟩
      | position position =>
          apply relTriple_bind (relTriple_refl LazyRevealProbe.sampleHashOutput)
          intro leftSample rightSample hsample
          subst rightSample
          simp only [runPermissiveFromTable, OracleComp.construct_pure]
          exact relTriple_pure_pure
            ⟨hstate.materialize_other (.position position) leftSample hne,
              rfl, rfl, rfl,
              hcache.update_same_hidden_of_ne (.position position) leftSample hne⟩

theorem rootHiddenPermissiveRelates_publishCoordinate_of_ne
    (target : Position) (leftOutput rightOutput : HashOutput)
    (coordinate : Coordinate) (hne : coordinate ≠ .position target) :
    RootHiddenPermissiveRelates target leftOutput rightOutput
      (publishCoordinate coordinate) (publishCoordinate coordinate) := by
  intro leftState rightState hstate fuel table leftCache rightCache hcache
  unfold publishCoordinate LazyRevealProbe.publishQuery
  rw [StateT.run_liftM, StateT.run_liftM,
    runPermissiveFromTable_publish_query_bind, runPermissiveFromTable_publish_query_bind]
  simp only [runPermissiveFromTable, OracleComp.construct_pure]
  exact relTriple_pure_pure
    ⟨hstate.publish_of_ne coordinate hne, rfl, rfl, trivial, hcache⟩

theorem rootHiddenPermissiveRelates_revealCoordinateOutput_of_ne
    (target : Position) (leftOutput rightOutput : HashOutput)
    (coordinate : Coordinate) (hne : coordinate ≠ .position target) :
    RootHiddenPermissiveRelates target leftOutput rightOutput
      (revealCoordinateOutput coordinate) (revealCoordinateOutput coordinate) := by
  intro leftState rightState hstate fuel table leftCache rightCache hcache
  rw [revealCoordinateOutput_run_eq, revealCoordinateOutput_run_eq,
    LazyRevealProbe.revealQuery, runPermissiveFromTable_reveal_query_bind,
    runPermissiveFromTable_reveal_query_bind]
  have hvalue := hstate.other_values coordinate hne
  cases hleft : leftState.values coordinate with
  | some output =>
      have hright : rightState.values coordinate = some output := by
        rw [← hvalue]
        exact hleft
      simp only [hright, runPermissiveFromTable, OracleComp.construct_pure]
      exact relTriple_pure_pure ⟨hstate, rfl, rfl, rfl,
        hcache.update_same_hidden_of_ne coordinate output hne⟩
  | none =>
      have hright : rightState.values coordinate = none := by
        rw [← hvalue]
        exact hleft
      simp only [hright]
      cases coordinate with
      | chainStart lay tree leafIdx chainIdx =>
          simp only [runPermissiveFromTable, OracleComp.construct_pure]
          exact relTriple_pure_pure
            ⟨hstate.materialize_other (.chainStart lay tree leafIdx chainIdx)
                (table ⟨lay, tree, leafIdx, chainIdx⟩) hne,
              rfl, rfl, rfl,
              hcache.update_same_hidden_of_ne (.chainStart lay tree leafIdx chainIdx)
                (table ⟨lay, tree, leafIdx, chainIdx⟩) hne⟩
      | position position =>
          apply relTriple_bind (relTriple_refl LazyRevealProbe.sampleHashOutput)
          intro leftSample rightSample hsample
          subst rightSample
          simp only [runPermissiveFromTable, OracleComp.construct_pure]
          exact relTriple_pure_pure
            ⟨hstate.materialize_other (.position position) leftSample hne,
              rfl, rfl, rfl,
              hcache.update_same_hidden_of_ne (.position position) leftSample hne⟩

theorem rootHiddenPermissiveRelates_modifyOrdinary
    (target : Position) (leftOutput rightOutput : HashOutput)
    (input : HashInput) (output : HashOutput) :
    RootHiddenPermissiveRelates target leftOutput rightOutput
      (modify fun cache : SplitHashCache =>
        Function.update cache (.ordinary input) (some output))
      (modify fun cache : SplitHashCache =>
        Function.update cache (.ordinary input) (some output)) := by
  intro leftState rightState hstate fuel table leftCache rightCache hcache
  simp only [StateT.run_modify, runPermissiveFromTable, OracleComp.construct_pure]
  exact relTriple_pure_pure
    ⟨hstate, rfl, rfl, trivial, hcache.update_same_ordinary input output⟩

theorem rootHiddenPermissiveRelates_executeCandidate
    (target : Position) (leftOutput rightOutput : HashOutput)
    (candidate? : Option Probe) :
    RootHiddenPermissiveRelates target leftOutput rightOutput
      (executeCandidate? candidate?) (executeCandidate? candidate?) := by
  cases candidate? with
  | none => exact rootHiddenPermissiveRelates_pure target leftOutput rightOutput ()
  | some candidate => exact rootHiddenPermissiveRelates_probe target leftOutput rightOutput candidate

theorem rootHiddenPermissiveRelates_resolvePublicKnownInput_of_ne
    (parameter : PublicParameter)
    (target : Position) (leftOutput rightOutput : HashOutput)
    (publicState : LazyRevealProbe.State Coordinate)
    (coordinate : Coordinate) (hne : coordinate ≠ .position target)
    (input : HashInput) :
    RootHiddenPermissiveRelates target leftOutput rightOutput
      (resolvePublicKnownInput parameter publicState coordinate input)
      (resolvePublicKnownInput parameter publicState coordinate input) := by
  unfold resolvePublicKnownInput
  cases hknown : purePeekTableInput parameter publicState coordinate with
  | none =>
      exact rootHiddenPermissiveRelates_splitHashQuery_ordinary target leftOutput rightOutput input
  | some knownInput =>
      by_cases heq : knownInput = input
      · simp only [heq, ↓reduceIte]
        exact (rootHiddenPermissiveRelates_revealCoordinateOutput_of_ne target leftOutput
          rightOutput coordinate hne).bind fun leftValue rightValue hvalue => by
            subst rightValue
            exact (rootHiddenPermissiveRelates_publishCoordinate_of_ne target leftOutput
              rightOutput coordinate hne).bind fun _ _ _ =>
                (rootHiddenPermissiveRelates_modifyOrdinary target leftOutput rightOutput input
                  leftValue).bind fun _ _ _ =>
                    rootHiddenPermissiveRelates_pure target leftOutput rightOutput leftValue
      · simp only [heq, ↓reduceIte]
        exact rootHiddenPermissiveRelates_splitHashQuery_ordinary target leftOutput rightOutput input

theorem rootHiddenPermissiveRelates_probingHashQueryAfterPublicPlan
    (parameter : PublicParameter)
    (target : Position) (leftOutput rightOutput : HashOutput)
    (input : HashInput) (publicState : LazyRevealProbe.State Coordinate)
    (plan : PlannedHashQuery)
    (hsafe : plan.action ≠ .resolve (.position target)) :
    RootHiddenPermissiveRelates target leftOutput rightOutput
      (probingHashQueryAfterPublicPlan parameter input publicState plan)
      (probingHashQueryAfterPublicPlan parameter input publicState plan) := by
  unfold probingHashQueryAfterPublicPlan
  exact (rootHiddenPermissiveRelates_executeCandidate target leftOutput rightOutput
    plan.candidate?).bind fun _ _ _ => by
      cases haction : plan.action with
      | ordinary =>
          exact rootHiddenPermissiveRelates_splitHashQuery_ordinary target leftOutput
            rightOutput input
      | resolve coordinate =>
          have hne : coordinate ≠ .position target := by
            intro heq
            apply hsafe
            rw [haction, heq]
          exact rootHiddenPermissiveRelates_resolvePublicKnownInput_of_ne parameter target
            leftOutput rightOutput publicState coordinate hne input

theorem rootHiddenPermissiveRelates_revealPublishedCoordinate_of_ne
    (target : Position) (leftOutput rightOutput : HashOutput)
    (coordinate : Coordinate) (hne : coordinate ≠ .position target) :
    RootHiddenPermissiveRelates target leftOutput rightOutput
      (revealPublishedCoordinate coordinate) (revealPublishedCoordinate coordinate) := by
  unfold revealPublishedCoordinate
  exact (rootHiddenPermissiveRelates_revealCoordinate_of_ne target leftOutput rightOutput
    coordinate hne).bind fun leftValue rightValue hvalue =>
      (rootHiddenPermissiveRelates_publishCoordinate_of_ne target leftOutput rightOutput
        coordinate hne).bind fun _ _ _ => by
          subst rightValue
          exact rootHiddenPermissiveRelates_pure target leftOutput rightOutput leftValue

def RootHiddenPermissiveTargetRevealRel
    (target : Position) (leftOutput rightOutput : HashOutput) :
    Option (CleanRunResult (Digest × SplitHashCache)) →
      Option (CleanRunResult (Digest × SplitHashCache)) → Prop
  | some left, some right =>
      RootHiddenStateRel target leftOutput rightOutput left.state right.state ∧
        left.remaining = right.remaining ∧ left.table = right.table ∧
        left.value.1 = truncateHash leftOutput ∧
        right.value.1 = truncateHash rightOutput ∧
        RootHiddenCacheRel target leftOutput rightOutput left.value.2 right.value.2
  | none, none => True
  | _, _ => False

theorem relTriple_rootHiddenPermissive_revealPosition_target
    (target : Position) (leftOutput rightOutput : HashOutput)
    (leftState rightState : LazyRevealProbe.State Coordinate)
    (hstate : RootHiddenStateRel target leftOutput rightOutput leftState rightState)
    (fuel : Nat) (table : OtsSecretIndex → HashOutput)
    (leftCache rightCache : SplitHashCache)
    (hcache : RootHiddenCacheRel target leftOutput rightOutput leftCache rightCache) :
    RelTriple
      (runPermissiveFromTable leftState fuel table ((revealPosition target).run leftCache))
      (runPermissiveFromTable rightState fuel table ((revealPosition target).run rightCache))
      (RootHiddenPermissiveTargetRevealRel target leftOutput rightOutput) := by
  rw [revealPosition_run, revealPosition_run, LazyRevealProbe.revealQuery,
    runPermissiveFromTable_reveal_query_bind, runPermissiveFromTable_reveal_query_bind,
    hstate.left_target, hstate.right_target]
  simp only [runPermissiveFromTable, OracleComp.construct_pure]
  exact relTriple_pure_pure
    ⟨hstate, rfl, rfl, rfl, rfl, hcache.update_targets⟩

theorem rootHiddenPermissiveRelates_sequenceFin
    (target : Position) (leftOutput rightOutput : HashOutput) {n : Nat}
    (left right : Fin n → StateT SplitHashCache
      (OracleComp (LazyRevealProbe.World Coordinate)) α)
    (hcomponent : ∀ index,
      RootHiddenPermissiveRelates target leftOutput rightOutput (left index) (right index)) :
    RootHiddenPermissiveRelates target leftOutput rightOutput
      (sequenceFin left) (sequenceFin right) := by
  induction n with
  | zero =>
      simp only [sequenceFin]
      exact rootHiddenPermissiveRelates_pure target leftOutput rightOutput Fin.elim0
  | succ n ih =>
      rw [sequenceFin, sequenceFin]
      exact (hcomponent 0).bind fun leftHead rightHead hhead =>
        (ih (fun index : Fin n => left index.succ) (fun index : Fin n => right index.succ)
          (fun index => hcomponent index.succ)).bind fun leftTail rightTail htail => by
            subst rightHead
            subst rightTail
            exact rootHiddenPermissiveRelates_pure target leftOutput rightOutput
              (Fin.cases leftHead leftTail : Fin (n + 1) → α)

theorem rootHiddenPermissiveRelates_ensureFullChain
    (target : Position) (leftOutput rightOutput : HashOutput)
    (lay : Layer) (tree : TreeIndex) (leafIdx : LeafIndex) (chainIdx : ChainIndex) :
    RootHiddenPermissiveRelates target leftOutput rightOutput
      (ensureFullChain lay tree leafIdx chainIdx)
      (ensureFullChain lay tree leafIdx chainIdx) := by
  unfold ensureFullChain
  exact (rootHiddenPermissiveRelates_sequenceFin target leftOutput rightOutput _ _
    (fun step => rootHiddenPermissiveRelates_ensureCoordinate target leftOutput rightOutput
      (.position (.chain lay tree leafIdx chainIdx step)))).bind fun _ _ _ =>
        rootHiddenPermissiveRelates_pure target leftOutput rightOutput ()

theorem rootHiddenPermissiveRelates_ensureOtsLeaf
    (target : Position) (leftOutput rightOutput : HashOutput)
    (lay : Layer) (tree : TreeIndex) (leafIdx : LeafIndex) :
    RootHiddenPermissiveRelates target leftOutput rightOutput
      (ensureOtsLeaf lay tree leafIdx) (ensureOtsLeaf lay tree leafIdx) := by
  unfold ensureOtsLeaf
  exact (rootHiddenPermissiveRelates_sequenceFin target leftOutput rightOutput _ _
    (fun chainIdx => rootHiddenPermissiveRelates_ensureFullChain target leftOutput rightOutput
      lay tree leafIdx chainIdx)).bind fun _ _ _ =>
        rootHiddenPermissiveRelates_ensureCoordinate target leftOutput rightOutput
          (.position (.leaf lay tree leafIdx))

theorem rootHiddenPermissiveRelates_ensureTreeNode
    (target : Position) (leftOutput rightOutput : HashOutput)
    (lay : Layer) (tree : TreeIndex) : ∀ level nodeIdx,
    RootHiddenPermissiveRelates target leftOutput rightOutput
      (ensureTreeNode lay tree level nodeIdx)
      (ensureTreeNode lay tree level nodeIdx)
  | 0, nodeIdx => by
      rw [ensureTreeNode]
      exact rootHiddenPermissiveRelates_ensureOtsLeaf target leftOutput rightOutput lay tree
        (leafOfNat nodeIdx)
  | level + 1, nodeIdx => by
      rw [ensureTreeNode]
      exact (rootHiddenPermissiveRelates_ensureTreeNode target leftOutput rightOutput lay tree level
        (2 * nodeIdx)).bind fun _ _ _ =>
          (rootHiddenPermissiveRelates_ensureTreeNode target leftOutput rightOutput lay tree level
            (2 * nodeIdx + 1)).bind fun _ _ _ => by
              by_cases hlevel : level < maxLayerHeight
              · rw [dif_pos hlevel]
                exact rootHiddenPermissiveRelates_ensureCoordinate target leftOutput rightOutput
                  (.position (.node lay tree ⟨level, hlevel⟩ (leafOfNat nodeIdx)))
              · rw [dif_neg hlevel]
                exact rootHiddenPermissiveRelates_pure target leftOutput rightOutput ()

theorem rootHiddenPermissiveRelates_ensureChainPrefix
    (target : Position) (leftOutput rightOutput : HashOutput)
    (lay : Layer) (tree : TreeIndex) (leafIdx : LeafIndex)
    (chainIdx : ChainIndex) (digit : Digit) :
    RootHiddenPermissiveRelates target leftOutput rightOutput
      (ensureChainPrefix lay tree leafIdx chainIdx digit)
      (ensureChainPrefix lay tree leafIdx chainIdx digit) := by
  unfold ensureChainPrefix
  exact (rootHiddenPermissiveRelates_sequenceFin target leftOutput rightOutput _ _
    (fun step => by
      by_cases hstep : step.val < digit.val
      · rw [if_pos hstep]
        exact rootHiddenPermissiveRelates_ensureCoordinate target leftOutput rightOutput
          (.position (.chain lay tree leafIdx chainIdx step))
      · rw [if_neg hstep]
        exact rootHiddenPermissiveRelates_pure target leftOutput rightOutput ())).bind
          fun _ _ _ => rootHiddenPermissiveRelates_pure target leftOutput rightOutput ()

theorem rootHiddenPermissiveRelates_ensureTreePath
    (target : Position) (leftOutput rightOutput : HashOutput)
    (lay : Layer) (tree : TreeIndex) (leafIdx : LeafIndex) :
    RootHiddenPermissiveRelates target leftOutput rightOutput
      (ensureTreePath lay tree leafIdx) (ensureTreePath lay tree leafIdx) := by
  unfold ensureTreePath
  exact (rootHiddenPermissiveRelates_sequenceFin target leftOutput rightOutput _ _
    (fun level => by
      by_cases hlevel : level.val < layerHeight lay
      · rw [if_pos hlevel]
        exact rootHiddenPermissiveRelates_ensureTreeNode target leftOutput rightOutput lay tree
          level.val (Nat.xor (leafIdx.val / 2 ^ level.val) 1)
      · rw [if_neg hlevel]
        exact rootHiddenPermissiveRelates_pure target leftOutput rightOutput ())).bind
          fun _ _ _ => rootHiddenPermissiveRelates_pure target leftOutput rightOutput ()

theorem rootHiddenPermissiveRelates_simulateQ
    {spec : OracleSpec ι}
    (target : Position) (leftOutput rightOutput : HashOutput)
    (leftImpl rightImpl : QueryImpl spec
      (StateT SplitHashCache (OracleComp (LazyRevealProbe.World Coordinate))))
    (himpl : ∀ query,
      RootHiddenPermissiveRelates target leftOutput rightOutput
        (leftImpl query) (rightImpl query))
    (computation : OracleComp spec α) :
    RootHiddenPermissiveRelates target leftOutput rightOutput
      (simulateQ leftImpl computation) (simulateQ rightImpl computation) := by
  induction computation using OracleComp.inductionOn with
  | pure value =>
      rw [simulateQ_pure, simulateQ_pure]
      exact rootHiddenPermissiveRelates_pure target leftOutput rightOutput value
  | query_bind query next ih =>
      rw [simulateQ_query_bind, simulateQ_query_bind]
      exact (himpl query).bind fun leftValue rightValue hvalue => by
        subst rightValue
        exact ih leftValue

theorem rootHiddenPermissiveRelates_ordinaryHashImpl
    (target : Position) (leftOutput rightOutput : HashOutput)
    (input : HashInput) :
    RootHiddenPermissiveRelates target leftOutput rightOutput
      (ordinaryHashImpl input) (ordinaryHashImpl input) :=
  rootHiddenPermissiveRelates_splitHashQuery_ordinary target leftOutput rightOutput input

theorem rootHiddenPermissiveRelates_maskedOtsSignFrom
    (target : Position) (leftOutput rightOutput : HashOutput)
    (parameter : PublicParameter) (lay : Layer) (tree : TreeIndex)
    (leafIdx : LeafIndex) (message : Digest) : ∀ attempts counter,
    RootHiddenPermissiveRelates target leftOutput rightOutput
      (maskedOtsSignFrom parameter lay tree leafIdx message attempts counter)
      (maskedOtsSignFrom parameter lay tree leafIdx message attempts counter)
  | 0, counter => by
      rw [maskedOtsSignFrom]
      exact rootHiddenPermissiveRelates_pure target leftOutput rightOutput none
  | attempts + 1, counter => by
      rw [maskedOtsSignFrom]
      apply (rootHiddenPermissiveRelates_simulateQ target leftOutput rightOutput
        ordinaryHashImpl ordinaryHashImpl
        (rootHiddenPermissiveRelates_ordinaryHashImpl target leftOutput rightOutput)
        (encode parameter lay tree leafIdx message
          (BitVec.ofNat counterBits counter))).bind
      intro leftEncoded rightEncoded hencoded
      subst rightEncoded
      cases leftEncoded with
      | none =>
          exact rootHiddenPermissiveRelates_maskedOtsSignFrom target leftOutput rightOutput
            parameter lay tree leafIdx message attempts (counter + 1)
      | some encoding =>
          exact (rootHiddenPermissiveRelates_sequenceFin target leftOutput rightOutput _ _
            (fun chainIdx =>
              rootHiddenPermissiveRelates_ensureChainPrefix target leftOutput rightOutput
                lay tree leafIdx chainIdx (encoding chainIdx))).bind fun _ _ _ =>
                  rootHiddenPermissiveRelates_pure target leftOutput rightOutput
                    (some (BitVec.ofNat counterBits counter, encoding))

theorem rootHiddenPermissiveRelates_maskedOtsSign
    (target : Position) (leftOutput rightOutput : HashOutput)
    (parameter : PublicParameter) (lay : Layer) (tree : TreeIndex)
    (leafIdx : LeafIndex) (message : Digest) :
    RootHiddenPermissiveRelates target leftOutput rightOutput
      (maskedOtsSign parameter lay tree leafIdx message)
      (maskedOtsSign parameter lay tree leafIdx message) :=
  rootHiddenPermissiveRelates_maskedOtsSignFrom target leftOutput rightOutput parameter lay tree
    leafIdx message encodingAttemptLimit 0

theorem rootHiddenPermissiveRelates_maskedOtsLayerAfterMessage
    (target : Position) (leftOutput rightOutput : HashOutput)
    (parameter : PublicParameter) (index : Index) (lay : Layer) (message : Digest) :
    RootHiddenPermissiveRelates target leftOutput rightOutput
      (maskedOtsLayerAfterMessage parameter index lay message)
      (maskedOtsLayerAfterMessage parameter index lay message) := by
  unfold maskedOtsLayerAfterMessage
  apply (rootHiddenPermissiveRelates_maskedOtsSign target leftOutput rightOutput parameter lay
    (treeIndexAt index lay) (leafIndexAt index lay) message).bind
  intro leftResult rightResult hresult
  subst rightResult
  cases leftResult with
  | none => exact rootHiddenPermissiveRelates_pure target leftOutput rightOutput none
  | some part =>
      exact (rootHiddenPermissiveRelates_ensureTreePath target leftOutput rightOutput lay
        (treeIndexAt index lay) (leafIndexAt index lay)).bind fun _ _ _ =>
          rootHiddenPermissiveRelates_pure target leftOutput rightOutput (some part)

theorem relTriple_rootHiddenPermissive_maskedTreeRoot_target
    (lay : Layer) (tree : TreeIndex)
    (leftOutput rightOutput : HashOutput)
    (leftState rightState : LazyRevealProbe.State Coordinate)
    (hstate : RootHiddenStateRel (layerRootPosition lay tree) leftOutput rightOutput
      leftState rightState)
    (fuel : Nat) (table : OtsSecretIndex → HashOutput)
    (leftCache rightCache : SplitHashCache)
    (hcache : RootHiddenCacheRel (layerRootPosition lay tree) leftOutput rightOutput
      leftCache rightCache) :
    RelTriple
      (runPermissiveFromTable leftState fuel table ((maskedTreeRoot lay tree).run leftCache))
      (runPermissiveFromTable rightState fuel table ((maskedTreeRoot lay tree).run rightCache))
      (RootHiddenPermissiveTargetRevealRel
        (layerRootPosition lay tree) leftOutput rightOutput) := by
  rw [maskedTreeRoot_eq_ensure_reveal, StateT.run_bind, StateT.run_bind,
    runPermissiveFromTable_bind, runPermissiveFromTable_bind]
  apply relTriple_bind
    (rootHiddenPermissiveRelates_ensureTreeNode (layerRootPosition lay tree) leftOutput rightOutput
      lay tree (layerHeight lay) 0 leftState rightState hstate fuel table leftCache rightCache
        hcache)
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
          rcases hresult with ⟨hnextState, hremaining, htable, _hvalue, hnextCache⟩
          simp only
          rw [← hremaining, ← htable]
          exact relTriple_rootHiddenPermissive_revealPosition_target
            (layerRootPosition lay tree) leftOutput rightOutput leftResult.state
            rightResult.state hnextState leftResult.remaining leftResult.table
            leftResult.value.2 rightResult.value.2 hnextCache

theorem relTriple_rootHiddenPermissive_maskedLayerMessage_target
    (parameter : PublicParameter)
    (ftsSecret : Index → FtsTree → FtsLeaf → Digest)
    (target : Position) (hroot : IsLayerRoot target)
    (index : Index) (lay : Layer)
    (htarget : layerMessagePosition index lay = target)
    (leftOutput rightOutput : HashOutput)
    (leftState rightState : LazyRevealProbe.State Coordinate)
    (hstate : RootHiddenStateRel target leftOutput rightOutput leftState rightState)
    (fuel : Nat) (table : OtsSecretIndex → HashOutput)
    (leftCache rightCache : SplitHashCache)
    (hcache : RootHiddenCacheRel target leftOutput rightOutput leftCache rightCache) :
    RelTriple
      (runPermissiveFromTable leftState fuel table
        ((maskedLayerMessage parameter ftsSecret index lay).run leftCache))
      (runPermissiveFromTable rightState fuel table
        ((maskedLayerMessage parameter ftsSecret index lay).run rightCache))
      (RootHiddenPermissiveTargetRevealRel target leftOutput rightOutput) := by
  obtain ⟨below, hcomputation, hposition⟩ :=
    layerMessage_root_witness_of_isLayerRoot parameter ftsSecret target hroot index lay htarget
  have htargetRoot : target = layerRootPosition below (treeIndexAt index below) :=
    htarget.symm.trans hposition
  rw [hcomputation]
  rw [htargetRoot] at hstate hcache ⊢
  exact relTriple_rootHiddenPermissive_maskedTreeRoot_target below (treeIndexAt index below)
    leftOutput rightOutput leftState rightState hstate fuel table leftCache rightCache hcache

theorem rootHiddenPermissiveRelates_maskedSignLayer_comparison_actual
    (parameter : PublicParameter)
    (ftsSecret : Index → FtsTree → FtsLeaf → Digest)
    (target : Position) (hroot : IsLayerRoot target)
    (index : Index) (lay : Layer)
    (htarget : layerMessagePosition index lay = target)
    (leftOutput rightOutput : HashOutput) :
    RootHiddenPermissiveRelates target leftOutput rightOutput
      (maskedSignLayerWithComparisonRoot parameter ftsSecret index lay
        (truncateHash rightOutput))
      (maskedSignLayer parameter ftsSecret index lay) := by
  intro leftState rightState hstate fuel table leftCache rightCache hcache
  unfold maskedSignLayerWithComparisonRoot maskedSignLayer
  rw [StateT.run_bind, StateT.run_bind, runPermissiveFromTable_bind,
    runPermissiveFromTable_bind]
  apply relTriple_bind
    (relTriple_rootHiddenPermissive_maskedLayerMessage_target parameter ftsSecret target hroot
      index lay htarget leftOutput rightOutput leftState rightState hstate fuel table leftCache
      rightCache hcache)
  intro leftMessage rightMessage hmessage
  cases leftMessage with
  | none =>
      cases rightMessage with
      | none => exact relTriple_pure_pure trivial
      | some rightMessage => simp [RootHiddenPermissiveTargetRevealRel] at hmessage
  | some leftMessage =>
      cases rightMessage with
      | none => simp [RootHiddenPermissiveTargetRevealRel] at hmessage
      | some rightMessage =>
          rcases hmessage with ⟨hnextState, hremaining, htable, _hleftMessage,
            hrightMessage, hnextCache⟩
          simp only
          rw [← hremaining, ← htable, hrightMessage]
          exact rootHiddenPermissiveRelates_maskedOtsLayerAfterMessage target leftOutput
            rightOutput parameter index lay (truncateHash rightOutput) leftMessage.state
            rightMessage.state hnextState leftMessage.remaining leftMessage.table
            leftMessage.value.2 rightMessage.value.2 hnextCache

theorem rootHiddenPermissiveRelates_maskedTreeRoot_of_ne
    (target : Position) (leftOutput rightOutput : HashOutput)
    (lay : Layer) (tree : TreeIndex)
    (hne : layerRootPosition lay tree ≠ target) :
    RootHiddenPermissiveRelates target leftOutput rightOutput
      (maskedTreeRoot lay tree) (maskedTreeRoot lay tree) := by
  rw [maskedTreeRoot_eq_ensure_reveal]
  exact (rootHiddenPermissiveRelates_ensureTreeNode target leftOutput rightOutput lay tree
    (layerHeight lay) 0).bind fun _ _ _ =>
      rootHiddenPermissiveRelates_revealCoordinate_of_ne target leftOutput rightOutput
        (.position (layerRootPosition lay tree)) (by simpa using hne)

theorem rootHiddenPermissiveRelates_maskedLayerMessage_of_ne
    (parameter : PublicParameter)
    (ftsSecret : Index → FtsTree → FtsLeaf → Digest)
    (target : Position) (leftOutput rightOutput : HashOutput)
    (index : Index) (lay : Layer)
    (hne : layerMessagePosition index lay ≠ target) :
    RootHiddenPermissiveRelates target leftOutput rightOutput
      (maskedLayerMessage parameter ftsSecret index lay)
      (maskedLayerMessage parameter ftsSecret index lay) := by
  fin_cases lay
  · rw [maskedLayerMessage, dif_pos (by decide)]
    apply rootHiddenPermissiveRelates_maskedTreeRoot_of_ne
    simpa [layerMessagePosition_top, layerRootPosition]
  · rw [maskedLayerMessage, dif_pos (by decide)]
    apply rootHiddenPermissiveRelates_maskedTreeRoot_of_ne
    simpa [layerMessagePosition_middle, layerRootPosition]
  · rw [maskedLayerMessage, dif_neg (by decide)]
    exact rootHiddenPermissiveRelates_simulateQ target leftOutput rightOutput ordinaryHashImpl
      ordinaryHashImpl (rootHiddenPermissiveRelates_ordinaryHashImpl target leftOutput rightOutput)
        (ftsKey parameter index (ftsSecret index))

theorem rootHiddenPermissiveRelates_maskedSignLayer_of_ne
    (parameter : PublicParameter)
    (ftsSecret : Index → FtsTree → FtsLeaf → Digest)
    (target : Position) (leftOutput rightOutput : HashOutput)
    (index : Index) (lay : Layer)
    (hne : layerMessagePosition index lay ≠ target) :
    RootHiddenPermissiveRelates target leftOutput rightOutput
      (maskedSignLayer parameter ftsSecret index lay)
      (maskedSignLayer parameter ftsSecret index lay) := by
  unfold maskedSignLayer
  exact (rootHiddenPermissiveRelates_maskedLayerMessage_of_ne parameter ftsSecret target
    leftOutput rightOutput index lay hne).bind fun leftMessage rightMessage hmessage => by
      subst rightMessage
      exact rootHiddenPermissiveRelates_maskedOtsLayerAfterMessage target leftOutput rightOutput
        parameter index lay leftMessage

theorem rootHiddenPermissiveRelates_maskedSignLayerWithTargetComparison_actual
    (parameter : PublicParameter)
    (ftsSecret : Index → FtsTree → FtsLeaf → Digest)
    (target : Position) (hroot : IsLayerRoot target)
    (leftOutput rightOutput : HashOutput)
    (index : Index) (lay : Layer) :
    RootHiddenPermissiveRelates target leftOutput rightOutput
      (maskedSignLayerWithTargetComparison parameter target (truncateHash rightOutput)
        ftsSecret index lay)
      (maskedSignLayer parameter ftsSecret index lay) := by
  unfold maskedSignLayerWithTargetComparison
  by_cases htarget : layerMessagePosition index lay = target
  · rw [if_pos htarget]
    exact rootHiddenPermissiveRelates_maskedSignLayer_comparison_actual parameter ftsSecret target
      hroot index lay htarget leftOutput rightOutput
  · rw [if_neg htarget]
    exact rootHiddenPermissiveRelates_maskedSignLayer_of_ne parameter ftsSecret target
      leftOutput rightOutput index lay htarget

theorem rootHiddenPermissiveRelates_maskedSignLayersWithTargetComparison_actual
    (parameter : PublicParameter)
    (ftsSecret : Index → FtsTree → FtsLeaf → Digest)
    (target : Position) (hroot : IsLayerRoot target)
    (leftOutput rightOutput : HashOutput) (index : Index) :
    RootHiddenPermissiveRelates target leftOutput rightOutput
      (maskedSignLayersWithTargetComparison parameter target (truncateHash rightOutput)
        ftsSecret index)
      (sequenceFin fun lay => maskedSignLayer parameter ftsSecret index lay) := by
  unfold maskedSignLayersWithTargetComparison
  exact rootHiddenPermissiveRelates_sequenceFin target leftOutput rightOutput _ _ fun lay =>
    rootHiddenPermissiveRelates_maskedSignLayerWithTargetComparison_actual parameter ftsSecret
      target hroot leftOutput rightOutput index lay

theorem rootHiddenPermissiveRelates_revealLayerValues
    (target : Position) (hroot : IsLayerRoot target)
    (leftOutput rightOutput : HashOutput)
    (index : Index) (lay : Layer) (encoding : ChainIndex → Digit) :
    RootHiddenPermissiveRelates target leftOutput rightOutput
      (revealLayerValues index lay encoding) (revealLayerValues index lay encoding) := by
  unfold revealLayerValues
  apply (rootHiddenPermissiveRelates_sequenceFin target leftOutput rightOutput _ _ fun chainIdx =>
    rootHiddenPermissiveRelates_revealPublishedCoordinate_of_ne target leftOutput rightOutput
      (chainValueCoordinate lay (treeIndexAt index lay) (leafIndexAt index lay) chainIdx
        (encoding chainIdx))
      (chainValueCoordinate_ne_layerRoot hroot lay (treeIndexAt index lay)
        (leafIndexAt index lay) chainIdx (encoding chainIdx))).bind
  intro leftValues rightValues hvalues
  subst rightValues
  apply (rootHiddenPermissiveRelates_sequenceFin target leftOutput rightOutput _ _ fun level => by
    by_cases hlevel : level.val < layerHeight lay
    · rw [if_pos hlevel]
      cases hzero : level.val with
      | zero =>
          exact rootHiddenPermissiveRelates_revealPublishedCoordinate_of_ne target leftOutput
            rightOutput (.position (.leaf lay (treeIndexAt index lay)
              (leafOfNat (Nat.xor (leafIndexAt index lay).val 1)))) (by
                obtain ⟨rootLay, rootTree, rfl⟩ := hroot
                simp [layerRootPosition])
      | succ current =>
          rw [Nat.add_one]
          simp only
          by_cases hcurrent : current < maxLayerHeight
          · rw [dif_pos hcurrent]
            exact rootHiddenPermissiveRelates_revealPublishedCoordinate_of_ne target leftOutput
              rightOutput (.position (.node lay (treeIndexAt index lay) ⟨current, hcurrent⟩
                (leafOfNat (Nat.xor ((leafIndexAt index lay).val / 2 ^ (current + 1)) 1))))
              (by
                intro heq
                exact (pathNode_ne_layerRoot hroot lay (treeIndexAt index lay) current hcurrent _
                  (by omega)) (Coordinate.position.inj heq))
          · rw [dif_neg hcurrent]
            exact rootHiddenPermissiveRelates_pure target leftOutput rightOutput 0
    · rw [if_neg hlevel]
      exact rootHiddenPermissiveRelates_pure target leftOutput rightOutput 0).bind
  intro leftPath rightPath hpath
  subst rightPath
  exact rootHiddenPermissiveRelates_pure target leftOutput rightOutput (leftValues, leftPath)

theorem rootHiddenPermissiveRelates_maskedSignAfterDigestWithTargetComparison_actual
    (parameter : PublicParameter)
    (ftsSecret : Index → FtsTree → FtsLeaf → Digest)
    (target : Position) (hroot : IsLayerRoot target)
    (leftOutput rightOutput : HashOutput)
    (randomness : Randomness) (index : Index) (leaves : DigestTree → FtsLeaf) :
    RootHiddenPermissiveRelates target leftOutput rightOutput
      (maskedSignAfterDigestWithTargetComparison parameter target (truncateHash rightOutput)
        ftsSecret randomness index leaves)
      (maskedSignAfterDigest parameter ftsSecret randomness index leaves) := by
  unfold maskedSignAfterDigestWithTargetComparison maskedSignAfterDigest
  apply (rootHiddenPermissiveRelates_simulateQ target leftOutput rightOutput ordinaryHashImpl
    ordinaryHashImpl (rootHiddenPermissiveRelates_ordinaryHashImpl target leftOutput rightOutput)
      (ftsOpen parameter index leaves (ftsSecret index))).bind
  intro leftPath rightPath hpath
  subst rightPath
  apply (rootHiddenPermissiveRelates_maskedSignLayersWithTargetComparison_actual parameter ftsSecret
    target hroot leftOutput rightOutput index).bind
  intro leftLayers rightLayers hlayers
  subst rightLayers
  cases hparts : traverseOption leftLayers with
  | none => exact rootHiddenPermissiveRelates_pure target leftOutput rightOutput none
  | some parts =>
      apply (rootHiddenPermissiveRelates_sequenceFin target leftOutput rightOutput _ _ fun lay =>
        rootHiddenPermissiveRelates_revealLayerValues target hroot leftOutput rightOutput index lay
          (parts lay).2).bind
      intro leftRevealed rightRevealed hrevealed
      subst rightRevealed
      let signature : Signature :=
        { randomness := randomness
          ftsSecret := fun tree => ftsSecret index tree (leaves (ftsIndexOf tree))
          ftsPath := leftPath
          counter := fun lay => (parts lay).1
          chainValue := fun lay => (leftRevealed lay).1
          authPath := flattenPaths fun lay => (leftRevealed lay).2 }
      exact rootHiddenPermissiveRelates_pure target leftOutput rightOutput (some signature)

theorem rootHiddenPermissiveRelates_ordinaryRomImpl
    (target : Position) (leftOutput rightOutput : HashOutput)
    (query : OracleWorld.Domain) :
    RootHiddenPermissiveRelates target leftOutput rightOutput
      (ordinaryRomImpl query) (ordinaryRomImpl query) := by
  cases query with
  | inl n => exact rootHiddenPermissiveRelates_splitUniformImpl target leftOutput rightOutput n
  | inr input => exact rootHiddenPermissiveRelates_ordinaryHashImpl target leftOutput rightOutput input

theorem rootHiddenPermissiveRelates_maskedSignWithTargetComparison_actual
    (parameter : PublicParameter) (publicRoot : Digest)
    (ftsSecret : Index → FtsTree → FtsLeaf → Digest)
    (target : Position) (hroot : IsLayerRoot target)
    (leftOutput rightOutput : HashOutput) (message : Message) :
    RootHiddenPermissiveRelates target leftOutput rightOutput
      (maskedSignWithTargetComparison parameter publicRoot target (truncateHash rightOutput)
        ftsSecret message)
      (maskedSign parameter publicRoot ftsSecret message) := by
  unfold maskedSignWithTargetComparison maskedSign
  let secretKey : SecretKey :=
    ⟨parameter, publicRoot, fun _ _ _ _ => 0, ftsSecret⟩
  apply (rootHiddenPermissiveRelates_simulateQ target leftOutput rightOutput ordinaryRomImpl
    ordinaryRomImpl (rootHiddenPermissiveRelates_ordinaryRomImpl target leftOutput rightOutput)
      (signDigestLoop digestAttemptLimit secretKey message)).bind
  intro leftSelected rightSelected hselected
  subst rightSelected
  cases leftSelected with
  | none => exact rootHiddenPermissiveRelates_pure target leftOutput rightOutput none
  | some selected =>
      exact rootHiddenPermissiveRelates_maskedSignAfterDigestWithTargetComparison_actual parameter
        ftsSecret target hroot leftOutput rightOutput selected.1 selected.2.1 selected.2.2

end SphincsSecurity.Concrete.OtsProbeSimulation
