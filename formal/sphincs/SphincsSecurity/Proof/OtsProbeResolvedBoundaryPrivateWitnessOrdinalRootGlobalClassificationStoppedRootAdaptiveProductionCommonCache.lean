import SphincsSecurity.Proof.OtsProbeResolvedBoundaryPrivateWitnessOrdinalRootGlobalClassificationStoppedRootAdaptiveProductionCommonPeekFree

/-!
# Hidden-cache quotient for common root production

The permissive selector's concrete actions depend on a split cache only through its ordinary
random-oracle projection. Hidden entries are outputs of reveals and are never read by these actions.
-/

namespace SphincsSecurity.Concrete.OtsProbeSimulation

open OracleComp OracleSpec
open OracleComp.ProgramLogic.Relational

def PermissiveOrdinaryCacheRel :
    Option (CleanRunResult (α × SplitHashCache)) →
      Option (CleanRunResult (α × SplitHashCache)) → Prop
  | none, none => True
  | some left, some right =>
      left.state = right.state ∧ left.remaining = right.remaining ∧
        left.table = right.table ∧ left.value.1 = right.value.1 ∧
        ordinaryQueryCache left.value.2 = ordinaryQueryCache right.value.2
  | _, _ => False

def PermissiveOrdinaryCacheCouples
    (computation : StateT SplitHashCache
      (OracleComp (LazyRevealProbe.World Coordinate)) α) : Prop :=
  ∀ leftCache rightCache,
    ordinaryQueryCache leftCache = ordinaryQueryCache rightCache →
    ∀ state fuel table,
      RelTriple
        (runPermissiveFromTable state fuel table (computation.run leftCache))
        (runPermissiveFromTable state fuel table (computation.run rightCache))
        PermissiveOrdinaryCacheRel

theorem runPermissiveFromTable_uniform_query_bind
    (state : LazyRevealProbe.State Coordinate) (fuel n : Nat)
    (table : OtsSecretIndex → HashOutput)
    (next : Fin (n + 1) → OracleComp (LazyRevealProbe.World Coordinate) α) :
    runPermissiveFromTable state fuel table
        ((liftM (OracleSpec.query (spec := LazyRevealProbe.World Coordinate)
          (.uniform n)) :
            OracleComp (LazyRevealProbe.World Coordinate) (Fin (n + 1))) >>= next) = (do
      let output ← liftM (unifSpec.query n)
      runPermissiveFromTable state fuel table (next output)) := by
  rfl

theorem runPermissiveFromTable_hashOutput_query_bind
    (state : LazyRevealProbe.State Coordinate) (fuel : Nat)
    (table : OtsSecretIndex → HashOutput)
    (next : HashOutput → OracleComp (LazyRevealProbe.World Coordinate) α) :
    runPermissiveFromTable state fuel table
        ((liftM (OracleSpec.query (spec := LazyRevealProbe.World Coordinate) .hashOutput) :
            OracleComp (LazyRevealProbe.World Coordinate) HashOutput) >>= next) = (do
      let output ← LazyRevealProbe.sampleHashOutput
      runPermissiveFromTable state fuel table (next output)) := by
  rfl

theorem runPermissiveFromTable_ensure_query_bind
    (state : LazyRevealProbe.State Coordinate) (fuel : Nat)
    (table : OtsSecretIndex → HashOutput) (coordinate : Coordinate)
    (next : Unit → OracleComp (LazyRevealProbe.World Coordinate) α) :
    runPermissiveFromTable state fuel table
        ((liftM (OracleSpec.query (spec := LazyRevealProbe.World Coordinate)
          (.ensure coordinate)) :
            OracleComp (LazyRevealProbe.World Coordinate) Unit) >>= next) =
      runPermissiveFromTable (state.ensure coordinate) fuel table (next ()) := by
  rfl

theorem runPermissiveFromTable_probe_query_bind
    (state : LazyRevealProbe.State Coordinate) (fuel : Nat)
    (table : OtsSecretIndex → HashOutput) (coordinate : Coordinate) (candidate : Digest)
    (next : Unit → OracleComp (LazyRevealProbe.World Coordinate) α) :
    runPermissiveFromTable state fuel table
        ((liftM (OracleSpec.query (spec := LazyRevealProbe.World Coordinate)
          (.probe coordinate candidate)) :
            OracleComp (LazyRevealProbe.World Coordinate) Unit) >>= next) =
      match fuel with
      | 0 => pure none
      | remaining + 1 =>
          if coordinate ∈ state.revealed then
            runPermissiveFromTable state remaining table (next ())
          else runPermissiveFromTable (state.addPending coordinate candidate)
            remaining table (next ()) := by
  rfl

theorem runPermissiveFromTable_peek_query_bind
    (state : LazyRevealProbe.State Coordinate) (fuel : Nat)
    (table : OtsSecretIndex → HashOutput) (coordinate : Coordinate)
    (next : Option HashOutput → OracleComp (LazyRevealProbe.World Coordinate) α) :
    runPermissiveFromTable state fuel table
        ((liftM (OracleSpec.query (spec := LazyRevealProbe.World Coordinate)
          (.peek coordinate)) :
            OracleComp (LazyRevealProbe.World Coordinate) (Option HashOutput)) >>= next) =
      runPermissiveFromTable state fuel table (next (state.values coordinate)) := by
  rfl

theorem runPermissiveFromTable_publish_query_bind
    (state : LazyRevealProbe.State Coordinate) (fuel : Nat)
    (table : OtsSecretIndex → HashOutput) (coordinate : Coordinate)
    (next : Unit → OracleComp (LazyRevealProbe.World Coordinate) α) :
    runPermissiveFromTable state fuel table
        ((liftM (OracleSpec.query (spec := LazyRevealProbe.World Coordinate)
          (.publish coordinate)) :
            OracleComp (LazyRevealProbe.World Coordinate) Unit) >>= next) =
      runPermissiveFromTable (state.publish coordinate) fuel table (next ()) := by
  rfl

theorem runPermissiveFromTable_reveal_query_bind
    (state : LazyRevealProbe.State Coordinate) (fuel : Nat)
    (table : OtsSecretIndex → HashOutput) (coordinate : Coordinate)
    (next : HashOutput → OracleComp (LazyRevealProbe.World Coordinate) α) :
    runPermissiveFromTable state fuel table
        ((liftM (OracleSpec.query (spec := LazyRevealProbe.World Coordinate)
          (.reveal coordinate)) :
            OracleComp (LazyRevealProbe.World Coordinate) HashOutput) >>= next) =
      (match state.values coordinate with
      | some output => runPermissiveFromTable state fuel table (next output)
      | none =>
          match coordinate with
          | .chainStart lay tree leafIdx chainIdx =>
              let output := table ⟨lay, tree, leafIdx, chainIdx⟩
              runPermissiveFromTable (state.materialize coordinate output) fuel table
                (next output)
          | .position _ => do
              let output ← LazyRevealProbe.sampleHashOutput
              runPermissiveFromTable (state.materialize coordinate output) fuel table
                (next output)) := by
  cases coordinate <;> rfl

theorem runPermissiveFromTable_bind
    (state : LazyRevealProbe.State Coordinate) (fuel : Nat)
    (table : OtsSecretIndex → HashOutput)
    (left : OracleComp (LazyRevealProbe.World Coordinate) α)
    (next : α → OracleComp (LazyRevealProbe.World Coordinate) β) :
    runPermissiveFromTable state fuel table (left >>= next) =
      runPermissiveFromTable state fuel table left >>= fun result =>
        match result with
        | none => pure none
        | some result =>
            runPermissiveFromTable result.state result.remaining result.table
              (next result.value) := by
  induction left using OracleComp.inductionOn generalizing state fuel with
  | pure value => simp [runPermissiveFromTable]
  | query_bind input continuation ih =>
      cases input with
      | uniform n =>
          rw [bind_assoc, runPermissiveFromTable_uniform_query_bind,
            runPermissiveFromTable_uniform_query_bind]
          simp only [bind_assoc]
          apply bind_congr
          intro output
          exact ih output state fuel
      | hashOutput =>
          rw [bind_assoc, runPermissiveFromTable_hashOutput_query_bind,
            runPermissiveFromTable_hashOutput_query_bind]
          simp only [bind_assoc]
          apply bind_congr
          intro output
          exact ih output state fuel
      | ensure coordinate =>
          rw [bind_assoc, runPermissiveFromTable_ensure_query_bind,
            runPermissiveFromTable_ensure_query_bind]
          exact ih () (state.ensure coordinate) fuel
      | probe coordinate candidate =>
          rw [bind_assoc, runPermissiveFromTable_probe_query_bind,
            runPermissiveFromTable_probe_query_bind]
          cases fuel with
          | zero => simp
          | succ remaining =>
              by_cases hrevealed : coordinate ∈ state.revealed
              · simp only [hrevealed, ↓reduceIte]
                exact ih () state remaining
              · simp only [hrevealed, ↓reduceIte]
                exact ih () (state.addPending coordinate candidate) remaining
      | peek coordinate =>
          rw [bind_assoc, runPermissiveFromTable_peek_query_bind,
            runPermissiveFromTable_peek_query_bind]
          exact ih (state.values coordinate) state fuel
      | publish coordinate =>
          rw [bind_assoc, runPermissiveFromTable_publish_query_bind,
            runPermissiveFromTable_publish_query_bind]
          exact ih () (state.publish coordinate) fuel
      | reveal coordinate =>
          rw [bind_assoc, runPermissiveFromTable_reveal_query_bind,
            runPermissiveFromTable_reveal_query_bind]
          cases hvalue : state.values coordinate with
          | some output => exact ih output state fuel
          | none =>
              cases coordinate with
              | chainStart lay tree leafIdx chainIdx =>
                  exact ih (table ⟨lay, tree, leafIdx, chainIdx⟩)
                    (state.materialize (.chainStart lay tree leafIdx chainIdx)
                      (table ⟨lay, tree, leafIdx, chainIdx⟩)) fuel
              | position position =>
                  simp only [bind_assoc]
                  apply bind_congr
                  intro output
                  exact ih output (state.materialize (.position position) output) fuel

theorem permissiveOrdinaryCacheCouples_pure (value : α) :
    PermissiveOrdinaryCacheCouples
      (pure value : StateT SplitHashCache
        (OracleComp (LazyRevealProbe.World Coordinate)) α) := by
  intro leftCache rightCache hcache state fuel table
  simp [runPermissiveFromTable, PermissiveOrdinaryCacheRel, hcache]

theorem PermissiveOrdinaryCacheCouples.bind
    {left : StateT SplitHashCache
      (OracleComp (LazyRevealProbe.World Coordinate)) α}
    {next : α → StateT SplitHashCache
      (OracleComp (LazyRevealProbe.World Coordinate)) β}
    (hleft : PermissiveOrdinaryCacheCouples left)
    (hnext : ∀ value, PermissiveOrdinaryCacheCouples (next value)) :
    PermissiveOrdinaryCacheCouples (left >>= next) := by
  intro leftCache rightCache hcache state fuel table
  rw [StateT.run_bind, StateT.run_bind, runPermissiveFromTable_bind,
    runPermissiveFromTable_bind]
  apply relTriple_bind (hleft leftCache rightCache hcache state fuel table)
  intro leftResult rightResult hresult
  cases leftResult with
  | none =>
      cases rightResult with
      | none => exact relTriple_pure_pure trivial
      | some rightResult => exact False.elim hresult
  | some leftResult =>
      cases rightResult with
      | none => exact False.elim hresult
      | some rightResult =>
          rcases hresult with ⟨hstate, hremaining, htable, hvalue, hnextCache⟩
          simp only
          rw [← hstate, ← hremaining, ← htable, ← hvalue]
          exact hnext leftResult.value.1 leftResult.value.2 rightResult.value.2 hnextCache
            leftResult.state leftResult.remaining leftResult.table

theorem permissiveOrdinaryCacheCouples_sequenceFin
    {n : Nat}
    (computation : Fin n → StateT SplitHashCache
      (OracleComp (LazyRevealProbe.World Coordinate)) α)
    (hcomponent : ∀ index, PermissiveOrdinaryCacheCouples (computation index)) :
    PermissiveOrdinaryCacheCouples (sequenceFin computation) := by
  induction n with
  | zero =>
      simp only [sequenceFin]
      exact permissiveOrdinaryCacheCouples_pure Fin.elim0
  | succ n ih =>
      rw [sequenceFin]
      exact (hcomponent 0).bind fun head =>
        (ih (fun index : Fin n => computation index.succ)
          (fun index => hcomponent index.succ)).bind fun tail =>
            permissiveOrdinaryCacheCouples_pure
              (Fin.cases head tail : Fin (n + 1) → α)

theorem permissiveOrdinaryCacheCouples_splitUniformImpl (n : Nat) :
    PermissiveOrdinaryCacheCouples (splitUniformImpl n) := by
  intro leftCache rightCache hcache state fuel table
  unfold splitUniformImpl LazyRevealProbe.uniformQuery
  rw [StateT.run_liftM, StateT.run_liftM,
    runPermissiveFromTable_uniform_query_bind,
    runPermissiveFromTable_uniform_query_bind]
  apply relTriple_bind
    (relTriple_refl (liftM (unifSpec.query n) : ProbComp (Fin (n + 1))))
  intro leftOutput rightOutput houtput
  subst rightOutput
  simp [runPermissiveFromTable, PermissiveOrdinaryCacheRel, hcache]

theorem permissiveOrdinaryCacheCouples_splitHashQuery_ordinary (input : HashInput) :
    PermissiveOrdinaryCacheCouples (splitHashQuery (.ordinary input)) := by
  intro leftCache rightCache hcache state fuel table
  rw [splitHashQuery_run_eq, splitHashQuery_run_eq]
  cases hleft : leftCache (.ordinary input) with
  | some output =>
      have hright : rightCache (.ordinary input) = some output := by
        change ordinaryQueryCache rightCache input = some output
        rw [← hcache]
        exact hleft
      simp [hright, runPermissiveFromTable, PermissiveOrdinaryCacheRel, hcache]
  | none =>
      have hright : rightCache (.ordinary input) = none := by
        change ordinaryQueryCache rightCache input = none
        rw [← hcache]
        exact hleft
      simp only [hright]
      unfold LazyRevealProbe.hashOutputQuery
      rw [runPermissiveFromTable_hashOutput_query_bind,
        runPermissiveFromTable_hashOutput_query_bind]
      apply relTriple_bind (relTriple_refl LazyRevealProbe.sampleHashOutput)
      intro leftOutput rightOutput houtput
      subst rightOutput
      simp only [runPermissiveFromTable, OracleComp.construct_pure]
      apply relTriple_pure_pure
      refine ⟨rfl, rfl, rfl, rfl, ?_⟩
      rw [ordinaryQueryCache_update, ordinaryQueryCache_update, hcache]

theorem permissiveOrdinaryCacheCouples_simulateQ
    {spec : OracleSpec ι}
    (impl : QueryImpl spec
      (StateT SplitHashCache
        (OracleComp (LazyRevealProbe.World Coordinate))))
    (himpl : ∀ query, PermissiveOrdinaryCacheCouples (impl query))
    (computation : OracleComp spec α) :
    PermissiveOrdinaryCacheCouples (simulateQ impl computation) := by
  induction computation using OracleComp.inductionOn with
  | pure value =>
      rw [simulateQ_pure]
      exact permissiveOrdinaryCacheCouples_pure value
  | query_bind query next ih =>
      rw [simulateQ_query_bind]
      exact (himpl query).bind fun output => ih output

theorem permissiveOrdinaryCacheCouples_simulateQ_ordinaryHashImpl
    (computation : OracleComp HashSpec α) :
    PermissiveOrdinaryCacheCouples (simulateQ ordinaryHashImpl computation) :=
  permissiveOrdinaryCacheCouples_simulateQ ordinaryHashImpl
    permissiveOrdinaryCacheCouples_splitHashQuery_ordinary computation

theorem permissiveOrdinaryCacheCouples_simulateQ_ordinaryRomImpl
    (computation : OracleComp OracleWorld α) :
    PermissiveOrdinaryCacheCouples (simulateQ ordinaryRomImpl computation) := by
  apply permissiveOrdinaryCacheCouples_simulateQ ordinaryRomImpl
  intro query
  cases query with
  | inl n => exact permissiveOrdinaryCacheCouples_splitUniformImpl n
  | inr input => exact permissiveOrdinaryCacheCouples_splitHashQuery_ordinary input

theorem permissiveOrdinaryCacheCouples_ensureCoordinate (coordinate : Coordinate) :
    PermissiveOrdinaryCacheCouples (ensureCoordinate coordinate) := by
  intro leftCache rightCache hcache state fuel table
  unfold ensureCoordinate
  rw [StateT.run_liftM, StateT.run_liftM, LazyRevealProbe.ensureQuery,
    runPermissiveFromTable_ensure_query_bind,
    runPermissiveFromTable_ensure_query_bind]
  simp [runPermissiveFromTable, PermissiveOrdinaryCacheRel, hcache]

theorem permissiveOrdinaryCacheCouples_probe (candidate : Probe) :
    PermissiveOrdinaryCacheCouples (probe candidate) := by
  intro leftCache rightCache hcache state fuel table
  unfold probe LazyRevealProbe.probeQuery
  rw [StateT.run_liftM, StateT.run_liftM,
    runPermissiveFromTable_probe_query_bind,
    runPermissiveFromTable_probe_query_bind]
  cases fuel with
  | zero => exact relTriple_pure_pure trivial
  | succ remaining =>
      by_cases hrevealed : candidate.coordinate ∈ state.revealed
      · simp [hrevealed, runPermissiveFromTable, PermissiveOrdinaryCacheRel, hcache]
      · simp [hrevealed, runPermissiveFromTable, PermissiveOrdinaryCacheRel, hcache]

theorem permissiveOrdinaryCacheCouples_revealCoordinateOutput (coordinate : Coordinate) :
    PermissiveOrdinaryCacheCouples (revealCoordinateOutput coordinate) := by
  intro leftCache rightCache hcache state fuel table
  rw [revealCoordinateOutput_run_eq, revealCoordinateOutput_run_eq,
    LazyRevealProbe.revealQuery, runPermissiveFromTable_reveal_query_bind,
    runPermissiveFromTable_reveal_query_bind]
  cases hvalue : state.values coordinate with
  | some output =>
      simp only [runPermissiveFromTable, OracleComp.construct_pure]
      exact relTriple_pure_pure ⟨rfl, rfl, rfl, rfl, by
        rw [ordinaryQueryCache_update_hidden, ordinaryQueryCache_update_hidden, hcache]⟩
  | none =>
      cases coordinate with
      | chainStart lay tree leafIdx chainIdx =>
          simp only [runPermissiveFromTable, OracleComp.construct_pure]
          exact relTriple_pure_pure ⟨rfl, rfl, rfl, rfl, by
            rw [ordinaryQueryCache_update_hidden, ordinaryQueryCache_update_hidden, hcache]⟩
      | position position =>
          apply relTriple_bind (relTriple_refl LazyRevealProbe.sampleHashOutput)
          intro leftOutput rightOutput houtput
          subst rightOutput
          simp only [runPermissiveFromTable, OracleComp.construct_pure]
          exact relTriple_pure_pure ⟨rfl, rfl, rfl, rfl, by
            rw [ordinaryQueryCache_update_hidden, ordinaryQueryCache_update_hidden, hcache]⟩

theorem permissiveOrdinaryCacheCouples_revealCoordinate (coordinate : Coordinate) :
    PermissiveOrdinaryCacheCouples (revealCoordinate coordinate) := by
  unfold revealCoordinate
  exact (permissiveOrdinaryCacheCouples_revealCoordinateOutput coordinate).bind fun _ =>
    permissiveOrdinaryCacheCouples_pure _

theorem permissiveOrdinaryCacheCouples_publishCoordinate (coordinate : Coordinate) :
    PermissiveOrdinaryCacheCouples (publishCoordinate coordinate) := by
  intro leftCache rightCache hcache state fuel table
  unfold publishCoordinate
  rw [StateT.run_liftM, StateT.run_liftM, LazyRevealProbe.publishQuery,
    runPermissiveFromTable_publish_query_bind,
    runPermissiveFromTable_publish_query_bind]
  simp [runPermissiveFromTable, PermissiveOrdinaryCacheRel, hcache]

theorem permissiveOrdinaryCacheCouples_modifyOrdinary
    (input : HashInput) (output : HashOutput) :
    PermissiveOrdinaryCacheCouples
      (modify fun cache : SplitHashCache =>
        Function.update cache (.ordinary input) (some output)) := by
  intro leftCache rightCache hcache state fuel table
  simp only [StateT.run_modify, runPermissiveFromTable, OracleComp.construct_pure]
  apply relTriple_pure_pure
  refine ⟨rfl, rfl, rfl, rfl, ?_⟩
  rw [ordinaryQueryCache_update, ordinaryQueryCache_update, hcache]

theorem permissiveOrdinaryCacheCouples_resolvePublicKnownInput
    (parameter : PublicParameter) (publicState : LazyRevealProbe.State Coordinate)
    (coordinate : Coordinate) (input : HashInput) :
    PermissiveOrdinaryCacheCouples
      (resolvePublicKnownInput parameter publicState coordinate input) := by
  unfold resolvePublicKnownInput
  cases hknown : purePeekTableInput parameter publicState coordinate with
  | none => exact permissiveOrdinaryCacheCouples_splitHashQuery_ordinary input
  | some knownInput =>
      by_cases heq : knownInput = input
      · simp only [heq, ↓reduceIte]
        exact (permissiveOrdinaryCacheCouples_revealCoordinateOutput coordinate).bind fun output =>
          (permissiveOrdinaryCacheCouples_publishCoordinate coordinate).bind fun _ =>
            (permissiveOrdinaryCacheCouples_modifyOrdinary input output).bind fun _ =>
              permissiveOrdinaryCacheCouples_pure output
      · simp only [heq, ↓reduceIte]
        exact permissiveOrdinaryCacheCouples_splitHashQuery_ordinary input

theorem permissiveOrdinaryCacheCouples_publicAction
    (parameter : PublicParameter) (input : HashInput)
    (publicState : LazyRevealProbe.State Coordinate) (action : PlannedHashAction) :
    PermissiveOrdinaryCacheCouples
      (probingHashQueryPublicAction parameter input publicState action) := by
  cases action with
  | ordinary => exact permissiveOrdinaryCacheCouples_splitHashQuery_ordinary input
  | resolve coordinate =>
      exact permissiveOrdinaryCacheCouples_resolvePublicKnownInput parameter publicState
        coordinate input

theorem permissiveOrdinaryCacheCouples_executeCandidate? (candidate : Option Probe) :
    PermissiveOrdinaryCacheCouples (executeCandidate? candidate) := by
  cases candidate with
  | none => exact permissiveOrdinaryCacheCouples_pure ()
  | some candidate => exact permissiveOrdinaryCacheCouples_probe candidate

theorem permissiveOrdinaryCacheCouples_rootAwarePublicPlan
    (parameter : PublicParameter) (input : HashInput)
    (publicState : LazyRevealProbe.State Coordinate) (plan : PlannedHashQuery) :
    PermissiveOrdinaryCacheCouples
      (probingHashQueryAfterRootAwarePublicPlan parameter input publicState plan) := by
  unfold probingHashQueryAfterRootAwarePublicPlan
  exact (permissiveOrdinaryCacheCouples_executeCandidate?
    (rootAwareCandidateForPlan? parameter input plan)).bind fun _ =>
      permissiveOrdinaryCacheCouples_publicAction parameter input publicState plan.action

theorem permissiveOrdinaryCacheCouples_ensureChainPrefix
    (lay : Layer) (tree : TreeIndex) (leafIdx : LeafIndex)
    (chainIdx : ChainIndex) (digit : Digit) :
    PermissiveOrdinaryCacheCouples (ensureChainPrefix lay tree leafIdx chainIdx digit) := by
  unfold ensureChainPrefix
  exact (permissiveOrdinaryCacheCouples_sequenceFin _ fun step => by
    split
    · exact permissiveOrdinaryCacheCouples_ensureCoordinate
        (.position (.chain lay tree leafIdx chainIdx step))
    · exact permissiveOrdinaryCacheCouples_pure ()).bind fun _ =>
      permissiveOrdinaryCacheCouples_pure ()

theorem permissiveOrdinaryCacheCouples_ensureFullChain
    (lay : Layer) (tree : TreeIndex) (leafIdx : LeafIndex) (chainIdx : ChainIndex) :
    PermissiveOrdinaryCacheCouples (ensureFullChain lay tree leafIdx chainIdx) := by
  unfold ensureFullChain
  exact (permissiveOrdinaryCacheCouples_sequenceFin _ fun step =>
    permissiveOrdinaryCacheCouples_ensureCoordinate
      (.position (.chain lay tree leafIdx chainIdx step))).bind fun _ =>
        permissiveOrdinaryCacheCouples_pure ()

theorem permissiveOrdinaryCacheCouples_ensureOtsLeaf
    (lay : Layer) (tree : TreeIndex) (leafIdx : LeafIndex) :
    PermissiveOrdinaryCacheCouples (ensureOtsLeaf lay tree leafIdx) := by
  unfold ensureOtsLeaf
  exact (permissiveOrdinaryCacheCouples_sequenceFin _ fun chainIdx =>
    permissiveOrdinaryCacheCouples_ensureFullChain lay tree leafIdx chainIdx).bind fun _ =>
      permissiveOrdinaryCacheCouples_ensureCoordinate (.position (.leaf lay tree leafIdx))

theorem permissiveOrdinaryCacheCouples_ensureTreeNode
    (lay : Layer) (tree : TreeIndex) : ∀ level nodeIdx,
    PermissiveOrdinaryCacheCouples (ensureTreeNode lay tree level nodeIdx)
  | 0, nodeIdx => permissiveOrdinaryCacheCouples_ensureOtsLeaf lay tree (leafOfNat nodeIdx)
  | level + 1, nodeIdx => by
      rw [ensureTreeNode]
      exact (permissiveOrdinaryCacheCouples_ensureTreeNode lay tree level
        (2 * nodeIdx)).bind fun _ =>
          (permissiveOrdinaryCacheCouples_ensureTreeNode lay tree level
            (2 * nodeIdx + 1)).bind fun _ => by
              split
              · exact permissiveOrdinaryCacheCouples_ensureCoordinate
                  (.position (.node lay tree ⟨level, by assumption⟩ (leafOfNat nodeIdx)))
              · exact permissiveOrdinaryCacheCouples_pure ()

theorem permissiveOrdinaryCacheCouples_ensureTreePath
    (lay : Layer) (tree : TreeIndex) (leafIdx : LeafIndex) :
    PermissiveOrdinaryCacheCouples (ensureTreePath lay tree leafIdx) := by
  unfold ensureTreePath
  exact (permissiveOrdinaryCacheCouples_sequenceFin _ fun level => by
    split
    · exact permissiveOrdinaryCacheCouples_ensureTreeNode lay tree level.val
        (Nat.xor (leafIdx.val / 2 ^ level.val) 1)
    · exact permissiveOrdinaryCacheCouples_pure ()).bind fun _ =>
      permissiveOrdinaryCacheCouples_pure ()

theorem permissiveOrdinaryCacheCouples_maskedTreeNode
    (lay : Layer) (tree : TreeIndex) : ∀ level nodeIdx,
    PermissiveOrdinaryCacheCouples (maskedTreeNode lay tree level nodeIdx)
  | level, nodeIdx => by
      unfold maskedTreeNode
      apply (permissiveOrdinaryCacheCouples_ensureTreeNode lay tree level nodeIdx).bind
      intro _
      cases level with
      | zero =>
          exact permissiveOrdinaryCacheCouples_revealCoordinate
            (.position (.leaf lay tree (leafOfNat nodeIdx)))
      | succ current =>
          rw [Nat.add_one]
          simp only
          split
          · exact permissiveOrdinaryCacheCouples_revealCoordinate
              (.position (.node lay tree ⟨current, by assumption⟩ (leafOfNat nodeIdx)))
          · exact permissiveOrdinaryCacheCouples_pure 0

theorem permissiveOrdinaryCacheCouples_maskedTreeRoot
    (lay : Layer) (tree : TreeIndex) :
    PermissiveOrdinaryCacheCouples (maskedTreeRoot lay tree) :=
  permissiveOrdinaryCacheCouples_maskedTreeNode lay tree (layerHeight lay) 0

theorem permissiveOrdinaryCacheCouples_maskedOtsSignFrom
    (parameter : PublicParameter) (lay : Layer) (tree : TreeIndex)
    (leafIdx : LeafIndex) (message : Digest) : ∀ attempts counter,
    PermissiveOrdinaryCacheCouples
      (maskedOtsSignFrom parameter lay tree leafIdx message attempts counter)
  | 0, _ => permissiveOrdinaryCacheCouples_pure none
  | attempts + 1, counter => by
      rw [maskedOtsSignFrom]
      exact (permissiveOrdinaryCacheCouples_simulateQ_ordinaryHashImpl
        (encode parameter lay tree leafIdx message
          (BitVec.ofNat counterBits counter))).bind fun encoded => by
            cases encoded with
            | none =>
                exact permissiveOrdinaryCacheCouples_maskedOtsSignFrom parameter lay tree
                  leafIdx message attempts (counter + 1)
            | some encoding =>
                exact (permissiveOrdinaryCacheCouples_sequenceFin _ fun chainIdx =>
                  permissiveOrdinaryCacheCouples_ensureChainPrefix lay tree leafIdx chainIdx
                    (encoding chainIdx)).bind fun _ => permissiveOrdinaryCacheCouples_pure _

theorem permissiveOrdinaryCacheCouples_maskedOtsSign
    (parameter : PublicParameter) (lay : Layer) (tree : TreeIndex)
    (leafIdx : LeafIndex) (message : Digest) :
    PermissiveOrdinaryCacheCouples (maskedOtsSign parameter lay tree leafIdx message) :=
  permissiveOrdinaryCacheCouples_maskedOtsSignFrom parameter lay tree leafIdx message
    encodingAttemptLimit 0

theorem permissiveOrdinaryCacheCouples_maskedLayerMessage
    (parameter : PublicParameter)
    (ftsSecret : Index → FtsTree → FtsLeaf → Digest) (index : Index) (lay : Layer) :
    PermissiveOrdinaryCacheCouples (maskedLayerMessage parameter ftsSecret index lay) := by
  unfold maskedLayerMessage
  split
  · exact permissiveOrdinaryCacheCouples_maskedTreeRoot _ _
  · exact permissiveOrdinaryCacheCouples_simulateQ_ordinaryHashImpl _

theorem permissiveOrdinaryCacheCouples_maskedSignLayer
    (parameter : PublicParameter)
    (ftsSecret : Index → FtsTree → FtsLeaf → Digest) (index : Index) (lay : Layer) :
    PermissiveOrdinaryCacheCouples (maskedSignLayer parameter ftsSecret index lay) := by
  unfold maskedSignLayer
  exact (permissiveOrdinaryCacheCouples_maskedLayerMessage parameter ftsSecret index lay).bind
    fun message =>
      (permissiveOrdinaryCacheCouples_maskedOtsSign parameter lay (treeIndexAt index lay)
        (leafIndexAt index lay) message).bind fun selected => by
          cases selected with
          | none => exact permissiveOrdinaryCacheCouples_pure none
          | some selected =>
              exact (permissiveOrdinaryCacheCouples_ensureTreePath lay
                (treeIndexAt index lay) (leafIndexAt index lay)).bind fun _ =>
                  permissiveOrdinaryCacheCouples_pure (some selected)

theorem permissiveOrdinaryCacheCouples_revealPublishedCoordinate
    (coordinate : Coordinate) :
    PermissiveOrdinaryCacheCouples (revealPublishedCoordinate coordinate) := by
  unfold revealPublishedCoordinate
  exact (permissiveOrdinaryCacheCouples_revealCoordinate coordinate).bind fun _ =>
    (permissiveOrdinaryCacheCouples_publishCoordinate coordinate).bind fun _ =>
      permissiveOrdinaryCacheCouples_pure _

theorem permissiveOrdinaryCacheCouples_revealLayerValues
    (index : Index) (lay : Layer) (encoding : ChainIndex → Digit) :
    PermissiveOrdinaryCacheCouples (revealLayerValues index lay encoding) := by
  unfold revealLayerValues
  exact (permissiveOrdinaryCacheCouples_sequenceFin _ fun chainIdx =>
    permissiveOrdinaryCacheCouples_revealPublishedCoordinate
      (chainValueCoordinate lay (treeIndexAt index lay) (leafIndexAt index lay)
        chainIdx (encoding chainIdx))).bind fun values =>
          (permissiveOrdinaryCacheCouples_sequenceFin _ fun level => by
            split
            · cases hzero : level.val with
              | zero =>
                  exact permissiveOrdinaryCacheCouples_revealPublishedCoordinate
                    (.position (.leaf lay (treeIndexAt index lay)
                      (leafOfNat (Nat.xor (leafIndexAt index lay).val 1))))
              | succ current =>
                  simp only
                  split
                  · exact permissiveOrdinaryCacheCouples_revealPublishedCoordinate
                      (.position (.node lay (treeIndexAt index lay)
                        ⟨current, by assumption⟩
                        (leafOfNat (Nat.xor
                          ((leafIndexAt index lay).val / 2 ^ (current + 1)) 1))))
                  · exact permissiveOrdinaryCacheCouples_pure 0
            · exact permissiveOrdinaryCacheCouples_pure 0).bind fun path =>
              permissiveOrdinaryCacheCouples_pure (values, path)

set_option maxHeartbeats 4000000 in
set_option maxRecDepth 100000 in
theorem permissiveOrdinaryCacheCouples_maskedSignAfterDigest
    (parameter : PublicParameter)
    (ftsSecret : Index → FtsTree → FtsLeaf → Digest)
    (randomness : Randomness) (index : Index) (leaves : DigestTree → FtsLeaf) :
    PermissiveOrdinaryCacheCouples
      (maskedSignAfterDigest parameter ftsSecret randomness index leaves) := by
  unfold maskedSignAfterDigest
  exact (permissiveOrdinaryCacheCouples_simulateQ_ordinaryHashImpl
    (ftsOpen parameter index leaves (ftsSecret index))).bind fun ftsPath =>
      (permissiveOrdinaryCacheCouples_sequenceFin _ fun lay =>
        permissiveOrdinaryCacheCouples_maskedSignLayer parameter ftsSecret index lay).bind
        fun layers => by
          cases hparts : traverseOption layers with
          | none => exact permissiveOrdinaryCacheCouples_pure none
          | some parts =>
              exact (permissiveOrdinaryCacheCouples_sequenceFin _ fun lay =>
                permissiveOrdinaryCacheCouples_revealLayerValues index lay
                  (parts lay).2).bind fun revealed =>
                    permissiveOrdinaryCacheCouples_pure (some
                      (show Signature from
                      { randomness := randomness
                        ftsSecret := fun tree => ftsSecret index tree (leaves (ftsIndexOf tree))
                        ftsPath := ftsPath
                        counter := fun lay => (parts lay).1
                        chainValue := fun lay => (revealed lay).1
                        authPath := flattenPaths fun lay => (revealed lay).2 }))

set_option maxHeartbeats 4000000 in
set_option maxRecDepth 100000 in
theorem permissiveOrdinaryCacheCouples_maskedSign
    (parameter : PublicParameter) (root : Digest)
    (ftsSecret : Index → FtsTree → FtsLeaf → Digest) (message : Message) :
    PermissiveOrdinaryCacheCouples (maskedSign parameter root ftsSecret message) := by
  unfold maskedSign
  exact (permissiveOrdinaryCacheCouples_simulateQ_ordinaryRomImpl
    (signDigestLoop digestAttemptLimit
      ⟨parameter, root, fun _ _ _ _ => 0, ftsSecret⟩ message)).bind fun selected => by
        cases selected with
        | none => exact permissiveOrdinaryCacheCouples_pure none
        | some data =>
            exact permissiveOrdinaryCacheCouples_maskedSignAfterDigest parameter ftsSecret
              data.1 data.2.1 data.2.2

end SphincsSecurity.Concrete.OtsProbeSimulation
