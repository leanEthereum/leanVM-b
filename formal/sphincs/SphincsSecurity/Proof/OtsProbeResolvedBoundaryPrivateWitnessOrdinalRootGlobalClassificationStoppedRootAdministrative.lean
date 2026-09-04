import SphincsSecurity.Proof.OtsProbeResolvedBoundaryPrivateWitnessOrdinalRootGlobalClassificationStoppedRootAdaptiveObservation

/-!
# Administrative equivalence for materialized runs

Proof-only hidden-cache entries are write-only during materialized execution. This file packages
the resulting ordinary-cache equivalence without requiring the deferred context to remain valid or
completable after a recorded hit.
-/

namespace SphincsSecurity.Concrete.OtsProbeSimulation

open OracleComp OracleSpec
open OracleComp.ProgramLogic.Relational

def ObservedFuelRel :
    Option (ObservedCleanRunResult α) → Option (ObservedCleanRunResult α) → Prop
  | some left, some right =>
      left.state = right.state ∧ left.table = right.table ∧
        left.value = right.value ∧ left.observations = right.observations
  | none, none => True
  | _, _ => False

set_option maxRecDepth 100000 in
theorem relTriple_runObservedCleanFromTable_fuel_of_isQueryBoundP
    (computation : OracleComp (LazyRevealProbe.World Coordinate) α)
    (observations : List CleanProbeObservation)
    (state : LazyRevealProbe.State Coordinate) (leftFuel rightFuel bound : Nat)
    (table : OtsSecretIndex → HashOutput)
    (hbound : computation.IsQueryBoundP LazyRevealProbe.IsProbe bound)
    (hleftFuel : bound ≤ leftFuel) (hrightFuel : bound ≤ rightFuel) :
    RelTriple
      (runObservedCleanFromTable observations state leftFuel table computation)
      (runObservedCleanFromTable observations state rightFuel table computation)
      ObservedFuelRel := by
  induction computation using OracleComp.inductionOn generalizing
      observations state leftFuel rightFuel bound with
  | pure value =>
      simp only [runObservedCleanFromTable, OracleComp.construct_pure]
      exact relTriple_pure_pure ⟨rfl, rfl, rfl, rfl⟩
  | query_bind query next ih =>
      rw [OracleComp.isQueryBoundP_query_bind_iff] at hbound
      cases query with
      | uniform n =>
          simp only [runObservedCleanFromTable, OracleComp.construct_query_bind]
          apply relTriple_bind (relTriple_refl (liftM (unifSpec.query n)))
          intro leftOutput rightOutput houtput
          subst rightOutput
          exact ih leftOutput observations state leftFuel rightFuel bound
            (by simpa [LazyRevealProbe.IsProbe] using hbound.2 leftOutput)
            hleftFuel hrightFuel
      | hashOutput =>
          simp only [runObservedCleanFromTable, OracleComp.construct_query_bind]
          apply relTriple_bind (relTriple_refl LazyRevealProbe.sampleHashOutput)
          intro leftOutput rightOutput houtput
          subst rightOutput
          exact ih leftOutput observations state leftFuel rightFuel bound
            (by simpa [LazyRevealProbe.IsProbe] using hbound.2 leftOutput)
            hleftFuel hrightFuel
      | ensure coordinate =>
          simp only [runObservedCleanFromTable, OracleComp.construct_query_bind]
          exact ih () observations (state.ensure coordinate) leftFuel rightFuel bound
            (by simpa [LazyRevealProbe.IsProbe] using hbound.2 ()) hleftFuel hrightFuel
      | probe coordinate candidate =>
          have hpositive : 0 < bound := by
            simpa [LazyRevealProbe.IsProbe] using hbound.1
          cases leftFuel with
          | zero => omega
          | succ leftRemaining =>
              cases rightFuel with
              | zero => omega
              | succ rightRemaining =>
                  rw [runObservedCleanFromTable_probe_query_bind,
                    runObservedCleanFromTable_probe_query_bind]
                  by_cases hrevealed : coordinate ∈ state.revealed
                  · simp only [hrevealed, ↓reduceIte]
                    exact ih ()
                      (observations ++ [cleanProbeObservation state coordinate candidate])
                      state leftRemaining rightRemaining (bound - 1)
                      (by simpa [LazyRevealProbe.IsProbe] using hbound.2 ())
                      (by omega) (by omega)
                  · simp only [hrevealed, ↓reduceIte]
                    exact ih ()
                      (observations ++ [cleanProbeObservation state coordinate candidate])
                      (state.addPending coordinate candidate)
                      leftRemaining rightRemaining (bound - 1)
                      (by simpa [LazyRevealProbe.IsProbe] using hbound.2 ())
                      (by omega) (by omega)
      | peek coordinate =>
          simp only [runObservedCleanFromTable, OracleComp.construct_query_bind]
          exact ih (state.values coordinate) observations state leftFuel rightFuel bound
            (by simpa [LazyRevealProbe.IsProbe] using hbound.2 (state.values coordinate))
            hleftFuel hrightFuel
      | publish coordinate =>
          simp only [runObservedCleanFromTable, OracleComp.construct_query_bind]
          exact ih () observations (state.publish coordinate) leftFuel rightFuel bound
            (by simpa [LazyRevealProbe.IsProbe] using hbound.2 ()) hleftFuel hrightFuel
      | reveal coordinate =>
          rw [runObservedCleanFromTable_reveal_query_bind,
            runObservedCleanFromTable_reveal_query_bind]
          cases hvalue : state.values coordinate with
          | some output =>
              exact ih output observations state leftFuel rightFuel bound
                (by simpa [LazyRevealProbe.IsProbe] using hbound.2 output)
                hleftFuel hrightFuel
          | none =>
              cases coordinate with
              | chainStart lay tree leafIdx chainIdx =>
                  let output := table ⟨lay, tree, leafIdx, chainIdx⟩
                  by_cases hhit : state.hitAt
                      (.chainStart lay tree leafIdx chainIdx) output
                  · simp [output, hhit, ObservedFuelRel]
                  · simp only [output, hhit, ↓reduceIte]
                    exact ih output observations
                      (state.materialize (.chainStart lay tree leafIdx chainIdx) output)
                      leftFuel rightFuel bound
                      (by simpa [LazyRevealProbe.IsProbe] using hbound.2 output)
                      hleftFuel hrightFuel
              | position position =>
                  apply relTriple_bind (relTriple_refl LazyRevealProbe.sampleHashOutput)
                  intro leftOutput rightOutput houtput
                  subst rightOutput
                  by_cases hhit : state.hitAt (.position position) leftOutput
                  · simp [hhit, ObservedFuelRel]
                  · simp only [hhit, ↓reduceIte]
                    exact ih leftOutput observations
                      (state.materialize (.position position) leftOutput)
                      leftFuel rightFuel bound
                      (by simpa [LazyRevealProbe.IsProbe] using hbound.2 leftOutput)
                      hleftFuel hrightFuel

def OrdinaryCacheCleanSameRel :
    Option (CleanRunResult (α × SplitHashCache)) →
      Option (CleanRunResult (α × SplitHashCache)) → Prop
  | some left, some right =>
      left.state = right.state ∧ left.remaining = right.remaining ∧
        left.table = right.table ∧ left.value.1 = right.value.1 ∧
        ordinaryQueryCache left.value.2 = ordinaryQueryCache right.value.2
  | none, none => True
  | _, _ => False

def OrdinaryCacheCouples
    (computation : StateT SplitHashCache
      (OracleComp (LazyRevealProbe.World Coordinate)) α) : Prop :=
  ∀ leftCache rightCache,
    ordinaryQueryCache leftCache = ordinaryQueryCache rightCache →
    ∀ state fuel table,
      RelTriple
        (runCleanFromTable state fuel table (computation.run leftCache))
        (runCleanFromTable state fuel table (computation.run rightCache))
        OrdinaryCacheCleanSameRel

def ObservedOrdinaryCacheRel
    (leftPrefix rightPrefix : List CleanProbeObservation) :
    Option (ObservedCleanRunResult (α × SplitHashCache)) →
      Option (ObservedCleanRunResult (α × SplitHashCache)) → Prop
  | some left, some right =>
      left.state = right.state ∧ left.remaining = right.remaining ∧
        left.table = right.table ∧ left.value.1 = right.value.1 ∧
        ordinaryQueryCache left.value.2 = ordinaryQueryCache right.value.2 ∧
        ∃ suffix,
          left.observations = leftPrefix ++ suffix ∧
            right.observations = rightPrefix ++ suffix
  | none, none => True
  | _, _ => False

theorem ordinaryCacheCouples_pure (value : α) :
    OrdinaryCacheCouples
      (pure value : StateT SplitHashCache
        (OracleComp (LazyRevealProbe.World Coordinate)) α) := by
  intro leftCache rightCache hcache state fuel table
  simp only [StateT.run_pure, runCleanFromTable, OracleComp.construct_pure]
  exact relTriple_pure_pure ⟨rfl, rfl, rfl, rfl, hcache⟩

theorem OrdinaryCacheCouples.bind
    {left : StateT SplitHashCache
      (OracleComp (LazyRevealProbe.World Coordinate)) α}
    {next : α → StateT SplitHashCache
      (OracleComp (LazyRevealProbe.World Coordinate)) β}
    (hleft : OrdinaryCacheCouples left)
    (hnext : ∀ value, OrdinaryCacheCouples (next value)) :
    OrdinaryCacheCouples (left >>= next) := by
  intro leftCache rightCache hcache state fuel table
  rw [StateT.run_bind, StateT.run_bind, runCleanFromTable_bind,
    runCleanFromTable_bind]
  apply relTriple_bind (hleft leftCache rightCache hcache state fuel table)
  intro leftResult rightResult hresult
  cases leftResult with
  | none =>
      cases rightResult with
      | none => exact relTriple_pure_pure trivial
      | some rightResult => simp [OrdinaryCacheCleanSameRel] at hresult
  | some leftResult =>
      cases rightResult with
      | none => simp [OrdinaryCacheCleanSameRel] at hresult
      | some rightResult =>
          rcases hresult with ⟨hstate, hremaining, htable, hvalue, hnextCache⟩
          simp only
          rw [← hstate, ← hremaining, ← htable, ← hvalue]
          exact hnext leftResult.value.1 leftResult.value.2 rightResult.value.2 hnextCache
            leftResult.state leftResult.remaining leftResult.table

theorem ordinaryCacheCouples_sequenceFin
    {n : Nat}
    (computation : Fin n → StateT SplitHashCache
      (OracleComp (LazyRevealProbe.World Coordinate)) α)
    (hcomponent : ∀ index, OrdinaryCacheCouples (computation index)) :
    OrdinaryCacheCouples (sequenceFin computation) := by
  induction n with
  | zero =>
      simp only [sequenceFin]
      exact ordinaryCacheCouples_pure Fin.elim0
  | succ n ih =>
      rw [sequenceFin]
      exact (hcomponent 0).bind fun _ =>
        (ih (fun index : Fin n => computation index.succ)
          (fun index => hcomponent index.succ)).bind fun _ =>
            ordinaryCacheCouples_pure _

theorem ordinaryCacheCouples_splitUniformImpl (n : Nat) :
    OrdinaryCacheCouples (splitUniformImpl n) := by
  intro leftCache rightCache hcache state fuel table
  unfold splitUniformImpl LazyRevealProbe.uniformQuery
  rw [StateT.run_liftM, StateT.run_liftM,
    runCleanFromTable_uniform_query_bind, runCleanFromTable_uniform_query_bind]
  apply relTriple_bind
    (relTriple_refl (liftM (unifSpec.query n) : ProbComp (Fin (n + 1))))
  intro leftOutput rightOutput houtput
  subst rightOutput
  simp only [runCleanFromTable, OracleComp.construct_pure]
  exact relTriple_pure_pure ⟨rfl, rfl, rfl, rfl, hcache⟩

theorem ordinaryCacheCouples_splitHashQuery_ordinary (input : HashInput) :
    OrdinaryCacheCouples (splitHashQuery (.ordinary input)) := by
  intro leftCache rightCache hcache state fuel table
  have hlookup := congrFun hcache input
  rw [splitHashQuery_run_eq, splitHashQuery_run_eq]
  cases hleft : leftCache (.ordinary input) with
  | some output =>
      have hright : rightCache (.ordinary input) = some output := by
        change ordinaryQueryCache rightCache input = some output
        rw [← hcache]
        exact hleft
      simp only [hright, runCleanFromTable, OracleComp.construct_pure]
      apply relTriple_pure_pure
      exact ⟨rfl, rfl, rfl, rfl, hcache⟩
  | none =>
      have hright : rightCache (.ordinary input) = none := by
        change ordinaryQueryCache rightCache input = none
        rw [← hcache]
        exact hleft
      simp only [hright]
      unfold LazyRevealProbe.hashOutputQuery
      rw [runCleanFromTable_hashOutput_query_bind,
        runCleanFromTable_hashOutput_query_bind]
      apply relTriple_bind (relTriple_refl LazyRevealProbe.sampleHashOutput)
      intro leftOutput rightOutput houtput
      subst rightOutput
      simp only [runCleanFromTable, OracleComp.construct_pure]
      apply relTriple_pure_pure
      refine ⟨rfl, rfl, rfl, rfl, ?_⟩
      rw [ordinaryQueryCache_update, ordinaryQueryCache_update, hcache]

theorem ordinaryCacheCouples_simulateQ
    {spec : OracleSpec ι}
    (impl : QueryImpl spec
      (StateT SplitHashCache
        (OracleComp (LazyRevealProbe.World Coordinate))))
    (himpl : ∀ query, OrdinaryCacheCouples (impl query))
    (computation : OracleComp spec α) :
    OrdinaryCacheCouples (simulateQ impl computation) := by
  induction computation using OracleComp.inductionOn with
  | pure value =>
      rw [simulateQ_pure]
      exact ordinaryCacheCouples_pure value
  | query_bind query next ih =>
      rw [simulateQ_query_bind]
      exact (himpl query).bind fun output => ih output

theorem ordinaryCacheCouples_simulateQ_ordinaryHashImpl
    (computation : OracleComp HashSpec α) :
    OrdinaryCacheCouples (simulateQ ordinaryHashImpl computation) :=
  ordinaryCacheCouples_simulateQ ordinaryHashImpl
    ordinaryCacheCouples_splitHashQuery_ordinary computation

theorem ordinaryCacheCouples_simulateQ_ordinaryRomImpl
    (computation : OracleComp OracleWorld α) :
    OrdinaryCacheCouples (simulateQ ordinaryRomImpl computation) := by
  apply ordinaryCacheCouples_simulateQ ordinaryRomImpl
  intro query
  cases query with
  | inl n => exact ordinaryCacheCouples_splitUniformImpl n
  | inr input => exact ordinaryCacheCouples_splitHashQuery_ordinary input

theorem ordinaryCacheCouples_ensureCoordinate (coordinate : Coordinate) :
    OrdinaryCacheCouples (ensureCoordinate coordinate) := by
  intro leftCache rightCache hcache state fuel table
  rw [runCleanFromTable_ensureCoordinate, runCleanFromTable_ensureCoordinate]
  exact relTriple_pure_pure ⟨rfl, rfl, rfl, rfl, hcache⟩

theorem ordinaryCacheCouples_probe (candidate : Probe) :
    OrdinaryCacheCouples (probe candidate) := by
  intro leftCache rightCache hcache state fuel table
  unfold probe LazyRevealProbe.probeQuery
  rw [StateT.run_liftM, StateT.run_liftM,
    runCleanFromTable_probe_query_bind, runCleanFromTable_probe_query_bind]
  cases fuel with
  | zero => exact relTriple_pure_pure trivial
  | succ remaining =>
      by_cases hrevealed : candidate.coordinate ∈ state.revealed
      · simp only [hrevealed, ↓reduceIte, runCleanFromTable,
          OracleComp.construct_pure]
        exact relTriple_pure_pure ⟨rfl, rfl, rfl, rfl, hcache⟩
      · simp only [hrevealed, ↓reduceIte, runCleanFromTable,
          OracleComp.construct_pure]
        exact relTriple_pure_pure ⟨rfl, rfl, rfl, rfl, hcache⟩

theorem ordinaryCacheCouples_peekCoordinate (coordinate : Coordinate) :
    OrdinaryCacheCouples (peekCoordinate coordinate) := by
  intro leftCache rightCache hcache state fuel table
  rw [peekCoordinate_run_eq, peekCoordinate_run_eq, LazyRevealProbe.peekQuery,
    runCleanFromTable_peek_query_bind, runCleanFromTable_peek_query_bind]
  simp only [runCleanFromTable, OracleComp.construct_pure]
  exact relTriple_pure_pure ⟨rfl, rfl, rfl, rfl, hcache⟩

theorem ordinaryCacheCouples_revealCoordinateOutput (coordinate : Coordinate) :
    OrdinaryCacheCouples (revealCoordinateOutput coordinate) := by
  intro leftCache rightCache hcache state fuel table
  rw [revealCoordinateOutput_run_eq, revealCoordinateOutput_run_eq,
    LazyRevealProbe.revealQuery, runCleanFromTable_reveal_query_bind,
    runCleanFromTable_reveal_query_bind]
  cases hvalue : state.values coordinate with
  | some output =>
      simp only [runCleanFromTable, OracleComp.construct_pure]
      exact relTriple_pure_pure ⟨rfl, rfl, rfl, rfl, by
        rw [ordinaryQueryCache_update_hidden, ordinaryQueryCache_update_hidden, hcache]⟩
  | none =>
      cases coordinate with
      | chainStart lay tree leafIdx chainIdx =>
          by_cases hhit : state.hitAt (.chainStart lay tree leafIdx chainIdx)
              (table ⟨lay, tree, leafIdx, chainIdx⟩)
          · simp [hhit, OrdinaryCacheCleanSameRel]
          · simp only [hhit, ↓reduceIte, runCleanFromTable, OracleComp.construct_pure]
            exact relTriple_pure_pure ⟨rfl, rfl, rfl, rfl, by
              rw [ordinaryQueryCache_update_hidden, ordinaryQueryCache_update_hidden, hcache]⟩
      | position position =>
          apply relTriple_bind (relTriple_refl LazyRevealProbe.sampleHashOutput)
          intro leftOutput rightOutput houtput
          subst rightOutput
          by_cases hhit : state.hitAt (.position position) leftOutput
          · simp [hhit, OrdinaryCacheCleanSameRel]
          · simp only [hhit, ↓reduceIte, runCleanFromTable, OracleComp.construct_pure]
            exact relTriple_pure_pure ⟨rfl, rfl, rfl, rfl, by
              rw [ordinaryQueryCache_update_hidden, ordinaryQueryCache_update_hidden, hcache]⟩

theorem ordinaryCacheCouples_revealCoordinate (coordinate : Coordinate) :
    OrdinaryCacheCouples (revealCoordinate coordinate) := by
  unfold revealCoordinate
  exact (ordinaryCacheCouples_revealCoordinateOutput coordinate).bind fun _ =>
    ordinaryCacheCouples_pure _

theorem ordinaryCacheCouples_publishCoordinate (coordinate : Coordinate) :
    OrdinaryCacheCouples (publishCoordinate coordinate) := by
  intro leftCache rightCache hcache state fuel table
  rw [runCleanFromTable_publishCoordinate, runCleanFromTable_publishCoordinate]
  exact relTriple_pure_pure ⟨rfl, rfl, rfl, rfl, hcache⟩

theorem ordinaryCacheCouples_modifyOrdinary (input : HashInput) (output : HashOutput) :
    OrdinaryCacheCouples
      (modify fun cache : SplitHashCache =>
        Function.update cache (.ordinary input) (some output)) := by
  intro leftCache rightCache hcache state fuel table
  simp only [StateT.run_modify, runCleanFromTable, OracleComp.construct_pure]
  apply relTriple_pure_pure
  refine ⟨rfl, rfl, rfl, rfl, ?_⟩
  rw [ordinaryQueryCache_update, ordinaryQueryCache_update, hcache]

theorem ordinaryCacheCouples_resolvePublicKnownInput
    (parameter : PublicParameter) (publicState : LazyRevealProbe.State Coordinate)
    (coordinate : Coordinate) (input : HashInput) :
    OrdinaryCacheCouples
      (resolvePublicKnownInput parameter publicState coordinate input) := by
  unfold resolvePublicKnownInput
  cases hknown : purePeekTableInput parameter publicState coordinate with
  | none => exact ordinaryCacheCouples_splitHashQuery_ordinary input
  | some knownInput =>
      by_cases heq : knownInput = input
      · simp only [heq, ↓reduceIte]
        exact (ordinaryCacheCouples_revealCoordinateOutput coordinate).bind fun output =>
          (ordinaryCacheCouples_publishCoordinate coordinate).bind fun _ =>
            (ordinaryCacheCouples_modifyOrdinary input output).bind fun _ =>
              ordinaryCacheCouples_pure output
      · simp only [heq, ↓reduceIte]
        exact ordinaryCacheCouples_splitHashQuery_ordinary input

theorem ordinaryCacheCouples_publicAction
    (parameter : PublicParameter) (input : HashInput)
    (publicState : LazyRevealProbe.State Coordinate) (action : PlannedHashAction) :
    OrdinaryCacheCouples
      (probingHashQueryPublicAction parameter input publicState action) := by
  cases action with
  | ordinary => exact ordinaryCacheCouples_splitHashQuery_ordinary input
  | resolve coordinate =>
      exact ordinaryCacheCouples_resolvePublicKnownInput parameter publicState coordinate input

theorem ordinaryCacheCouples_ensureChainPrefix
    (lay : Layer) (tree : TreeIndex) (leafIdx : LeafIndex)
    (chainIdx : ChainIndex) (digit : Digit) :
    OrdinaryCacheCouples (ensureChainPrefix lay tree leafIdx chainIdx digit) := by
  unfold ensureChainPrefix
  exact (ordinaryCacheCouples_sequenceFin _ fun step => by
    by_cases hstep : step.val < digit.val
    · rw [if_pos hstep]
      exact ordinaryCacheCouples_ensureCoordinate
        (.position (.chain lay tree leafIdx chainIdx step))
    · rw [if_neg hstep]
      exact ordinaryCacheCouples_pure ()).bind fun _ =>
        ordinaryCacheCouples_pure ()

theorem ordinaryCacheCouples_ensureFullChain
    (lay : Layer) (tree : TreeIndex) (leafIdx : LeafIndex)
    (chainIdx : ChainIndex) :
    OrdinaryCacheCouples (ensureFullChain lay tree leafIdx chainIdx) := by
  unfold ensureFullChain
  exact (ordinaryCacheCouples_sequenceFin _ fun step =>
    ordinaryCacheCouples_ensureCoordinate
      (.position (.chain lay tree leafIdx chainIdx step))).bind fun _ =>
        ordinaryCacheCouples_pure ()

theorem ordinaryCacheCouples_ensureOtsLeaf
    (lay : Layer) (tree : TreeIndex) (leafIdx : LeafIndex) :
    OrdinaryCacheCouples (ensureOtsLeaf lay tree leafIdx) := by
  unfold ensureOtsLeaf
  exact (ordinaryCacheCouples_sequenceFin _ fun chainIdx =>
    ordinaryCacheCouples_ensureFullChain lay tree leafIdx chainIdx).bind fun _ =>
      ordinaryCacheCouples_ensureCoordinate (.position (.leaf lay tree leafIdx))

theorem ordinaryCacheCouples_ensureTreeNode
    (lay : Layer) (tree : TreeIndex) : ∀ level nodeIdx,
    OrdinaryCacheCouples (ensureTreeNode lay tree level nodeIdx)
  | 0, nodeIdx =>
      ordinaryCacheCouples_ensureOtsLeaf lay tree (leafOfNat nodeIdx)
  | level + 1, nodeIdx => by
      rw [ensureTreeNode]
      exact (ordinaryCacheCouples_ensureTreeNode lay tree level (2 * nodeIdx)).bind fun _ =>
        (ordinaryCacheCouples_ensureTreeNode lay tree level (2 * nodeIdx + 1)).bind fun _ => by
          by_cases hlevel : level < maxLayerHeight
          · rw [dif_pos hlevel]
            exact ordinaryCacheCouples_ensureCoordinate
              (.position (.node lay tree ⟨level, hlevel⟩ (leafOfNat nodeIdx)))
          · rw [dif_neg hlevel]
            exact ordinaryCacheCouples_pure ()

theorem ordinaryCacheCouples_ensureTreePath
    (lay : Layer) (tree : TreeIndex) (leafIdx : LeafIndex) :
    OrdinaryCacheCouples (ensureTreePath lay tree leafIdx) := by
  unfold ensureTreePath
  exact (ordinaryCacheCouples_sequenceFin _ fun level => by
    by_cases hlevel : level.val < layerHeight lay
    · rw [if_pos hlevel]
      exact ordinaryCacheCouples_ensureTreeNode lay tree level.val
        (Nat.xor (leafIdx.val / 2 ^ level.val) 1)
    · rw [if_neg hlevel]
      exact ordinaryCacheCouples_pure ()).bind fun _ =>
        ordinaryCacheCouples_pure ()

theorem ordinaryCacheCouples_maskedTreeNode
    (lay : Layer) (tree : TreeIndex) : ∀ level nodeIdx,
    OrdinaryCacheCouples (maskedTreeNode lay tree level nodeIdx)
  | level, nodeIdx => by
      unfold maskedTreeNode
      apply (ordinaryCacheCouples_ensureTreeNode lay tree level nodeIdx).bind
      intro _
      cases level with
      | zero =>
          exact ordinaryCacheCouples_revealCoordinate
            (.position (.leaf lay tree (leafOfNat nodeIdx)))
      | succ current =>
          rw [Nat.add_one]
          simp only
          by_cases hlevel : current < maxLayerHeight
          · rw [dif_pos hlevel]
            exact ordinaryCacheCouples_revealCoordinate
              (.position (.node lay tree ⟨current, hlevel⟩ (leafOfNat nodeIdx)))
          · rw [dif_neg hlevel]
            exact ordinaryCacheCouples_pure 0

theorem ordinaryCacheCouples_maskedTreeRoot
    (lay : Layer) (tree : TreeIndex) :
    OrdinaryCacheCouples (maskedTreeRoot lay tree) :=
  ordinaryCacheCouples_maskedTreeNode lay tree (layerHeight lay) 0

theorem ordinaryCacheCouples_maskedOtsSignFrom
    (parameter : PublicParameter) (lay : Layer) (tree : TreeIndex)
    (leafIdx : LeafIndex) (message : Digest) : ∀ attempts counter,
    OrdinaryCacheCouples
      (maskedOtsSignFrom parameter lay tree leafIdx message attempts counter)
  | 0, counter => by
      rw [maskedOtsSignFrom]
      exact ordinaryCacheCouples_pure none
  | attempts + 1, counter => by
      rw [maskedOtsSignFrom]
      apply (ordinaryCacheCouples_simulateQ_ordinaryHashImpl
        (encode parameter lay tree leafIdx message
          (BitVec.ofNat counterBits counter))).bind
      intro encoded
      cases encoded with
      | none =>
          exact ordinaryCacheCouples_maskedOtsSignFrom parameter lay tree leafIdx message
            attempts (counter + 1)
      | some encoding =>
          exact (ordinaryCacheCouples_sequenceFin _ fun chainIdx =>
            ordinaryCacheCouples_ensureChainPrefix lay tree leafIdx chainIdx
              (encoding chainIdx)).bind fun _ =>
                ordinaryCacheCouples_pure
                  (some (BitVec.ofNat counterBits counter, encoding))

theorem ordinaryCacheCouples_maskedOtsSign
    (parameter : PublicParameter) (lay : Layer) (tree : TreeIndex)
    (leafIdx : LeafIndex) (message : Digest) :
    OrdinaryCacheCouples (maskedOtsSign parameter lay tree leafIdx message) :=
  ordinaryCacheCouples_maskedOtsSignFrom parameter lay tree leafIdx message
    encodingAttemptLimit 0

theorem ordinaryCacheCouples_maskedLayerMessage
    (parameter : PublicParameter)
    (ftsSecret : Index → FtsTree → FtsLeaf → Digest) (index : Index)
    (lay : Layer) :
    OrdinaryCacheCouples (maskedLayerMessage parameter ftsSecret index lay) := by
  unfold maskedLayerMessage
  by_cases hbelow : lay.val + 1 < numLayers
  · rw [dif_pos hbelow]
    exact ordinaryCacheCouples_maskedTreeRoot ⟨lay.val + 1, hbelow⟩
      (treeIndexAt index ⟨lay.val + 1, hbelow⟩)
  · rw [dif_neg hbelow]
    exact ordinaryCacheCouples_simulateQ_ordinaryHashImpl
      (ftsKey parameter index (ftsSecret index))

theorem ordinaryCacheCouples_maskedSignLayer
    (parameter : PublicParameter)
    (ftsSecret : Index → FtsTree → FtsLeaf → Digest) (index : Index)
    (lay : Layer) :
    OrdinaryCacheCouples (maskedSignLayer parameter ftsSecret index lay) := by
  unfold maskedSignLayer
  apply (ordinaryCacheCouples_maskedLayerMessage parameter ftsSecret index lay).bind
  intro message
  apply (ordinaryCacheCouples_maskedOtsSign parameter lay
    (treeIndexAt index lay) (leafIndexAt index lay) message).bind
  intro selected
  cases selected with
  | none => exact ordinaryCacheCouples_pure none
  | some selected =>
      exact (ordinaryCacheCouples_ensureTreePath lay
        (treeIndexAt index lay) (leafIndexAt index lay)).bind fun _ =>
          ordinaryCacheCouples_pure (some selected)

theorem ordinaryCacheCouples_revealPublishedCoordinate (coordinate : Coordinate) :
    OrdinaryCacheCouples (revealPublishedCoordinate coordinate) := by
  unfold revealPublishedCoordinate
  exact (ordinaryCacheCouples_revealCoordinate coordinate).bind fun _ =>
    (ordinaryCacheCouples_publishCoordinate coordinate).bind fun _ =>
      ordinaryCacheCouples_pure _

theorem ordinaryCacheCouples_revealLayerValues
    (index : Index) (lay : Layer) (encoding : ChainIndex → Digit) :
    OrdinaryCacheCouples (revealLayerValues index lay encoding) := by
  unfold revealLayerValues
  apply (ordinaryCacheCouples_sequenceFin _ fun chainIdx =>
    ordinaryCacheCouples_revealPublishedCoordinate
      (chainValueCoordinate lay (treeIndexAt index lay) (leafIndexAt index lay)
        chainIdx (encoding chainIdx))).bind
  intro values
  apply (ordinaryCacheCouples_sequenceFin _ fun level => by
    by_cases hlevel : level.val < layerHeight lay
    · rw [if_pos hlevel]
      cases hzero : level.val with
      | zero =>
          exact ordinaryCacheCouples_revealPublishedCoordinate
            (.position (.leaf lay (treeIndexAt index lay)
              (leafOfNat (Nat.xor (leafIndexAt index lay).val 1))))
      | succ current =>
          rw [Nat.add_one]
          simp only
          by_cases hcurrent : current < maxLayerHeight
          · rw [dif_pos hcurrent]
            exact ordinaryCacheCouples_revealPublishedCoordinate
              (.position (.node lay (treeIndexAt index lay) ⟨current, hcurrent⟩
                (leafOfNat
                  (Nat.xor ((leafIndexAt index lay).val / 2 ^ (current + 1)) 1))))
          · rw [dif_neg hcurrent]
            exact ordinaryCacheCouples_pure 0
    · rw [if_neg hlevel]
      exact ordinaryCacheCouples_pure 0).bind
  intro path
  exact ordinaryCacheCouples_pure (values, path)

theorem ordinaryCacheCouples_maskedSignAfterDigest
    (parameter : PublicParameter)
    (ftsSecret : Index → FtsTree → FtsLeaf → Digest)
    (randomness : Randomness) (index : Index) (leaves : DigestTree → FtsLeaf) :
    OrdinaryCacheCouples
      (maskedSignAfterDigest parameter ftsSecret randomness index leaves) := by
  unfold maskedSignAfterDigest
  apply (ordinaryCacheCouples_simulateQ_ordinaryHashImpl
    (ftsOpen parameter index leaves (ftsSecret index))).bind
  intro ftsPath
  apply (ordinaryCacheCouples_sequenceFin _ fun lay =>
    ordinaryCacheCouples_maskedSignLayer parameter ftsSecret index lay).bind
  intro layers
  cases hparts : traverseOption layers with
  | none => exact ordinaryCacheCouples_pure none
  | some parts =>
      apply (ordinaryCacheCouples_sequenceFin _ fun lay =>
        ordinaryCacheCouples_revealLayerValues index lay (parts lay).2).bind
      intro revealed
      let signature : Signature :=
        { randomness := randomness
          ftsSecret := fun tree => ftsSecret index tree (leaves (ftsIndexOf tree))
          ftsPath := ftsPath
          counter := fun lay => (parts lay).1
          chainValue := fun lay => (revealed lay).1
          authPath := flattenPaths fun lay => (revealed lay).2 }
      exact ordinaryCacheCouples_pure (some signature)

theorem ordinaryCacheCouples_maskedSign
    (parameter : PublicParameter) (root : Digest)
    (ftsSecret : Index → FtsTree → FtsLeaf → Digest) (message : Message) :
    OrdinaryCacheCouples (maskedSign parameter root ftsSecret message) := by
  unfold maskedSign
  apply (ordinaryCacheCouples_simulateQ_ordinaryRomImpl
    (signDigestLoop digestAttemptLimit
      ⟨parameter, root, fun _ _ _ _ => 0, ftsSecret⟩ message)).bind
  intro selected
  cases selected with
  | none => exact ordinaryCacheCouples_pure none
  | some data =>
      exact ordinaryCacheCouples_maskedSignAfterDigest parameter ftsSecret
        data.1 data.2.1 data.2.2

theorem relTriple_runObservedCleanFromTable_of_ordinaryCacheCouples_probeFree
    (computation : StateT SplitHashCache
      (OracleComp (LazyRevealProbe.World Coordinate)) α)
    (hcouples : OrdinaryCacheCouples computation)
    (hprobeFree : ProbeFree computation)
    (leftPrefix rightPrefix : List CleanProbeObservation)
    (state : LazyRevealProbe.State Coordinate) (fuel : Nat)
    (table : OtsSecretIndex → HashOutput) (leftCache rightCache : SplitHashCache)
    (hcache : ordinaryQueryCache leftCache = ordinaryQueryCache rightCache) :
    RelTriple
      (runObservedCleanFromTable leftPrefix state fuel table (computation.run leftCache))
      (runObservedCleanFromTable rightPrefix state fuel table (computation.run rightCache))
      (ObservedOrdinaryCacheRel leftPrefix rightPrefix) := by
  have hclean := hcouples leftCache rightCache hcache state fuel table
  have hstrength : RelTriple
      (runCleanFromTable state fuel table (computation.run leftCache))
      (runCleanFromTable state fuel table (computation.run rightCache))
      (fun left right => ObservedOrdinaryCacheRel leftPrefix rightPrefix
        (attachCleanProbeObservations leftPrefix left)
        (attachCleanProbeObservations rightPrefix right)) := by
    apply relTriple_post_mono hclean
    intro left right hrelation
    cases left with
    | none =>
        cases right with
        | none => trivial
        | some right => simp [OrdinaryCacheCleanSameRel] at hrelation
    | some left =>
        cases right with
        | none => simp [OrdinaryCacheCleanSameRel] at hrelation
        | some right =>
            rcases hrelation with ⟨hstate, hremaining, htable, hvalue, hcache⟩
            exact ⟨hstate, hremaining, htable, hvalue, hcache,
              [], by simp, by simp⟩
  have hpost : RelTriple
      (attachCleanProbeObservations leftPrefix <$>
        runCleanFromTable state fuel table (computation.run leftCache))
      (attachCleanProbeObservations rightPrefix <$>
        runCleanFromTable state fuel table (computation.run rightCache))
      (ObservedOrdinaryCacheRel leftPrefix rightPrefix) := by
    exact relTriple_map
      (f := attachCleanProbeObservations leftPrefix)
      (g := attachCleanProbeObservations rightPrefix) hstrength
  rw [map_attachCleanProbeObservations_runCleanFromTable_of_probeFree
      (computation.run leftCache) leftPrefix state fuel table (hprobeFree leftCache),
    map_attachCleanProbeObservations_runCleanFromTable_of_probeFree
      (computation.run rightCache) rightPrefix state fuel table (hprobeFree rightCache)] at hpost
  exact hpost

theorem ordinaryCacheCouples_rootAwarePublicPlan
    (parameter : PublicParameter) (input : HashInput)
    (publicState : LazyRevealProbe.State Coordinate) (plan : PlannedHashQuery) :
    OrdinaryCacheCouples
      (probingHashQueryAfterRootAwarePublicPlan parameter input publicState plan) := by
  unfold probingHashQueryAfterRootAwarePublicPlan executeCandidate?
  cases rootAwareCandidateForPlan? parameter input plan with
  | none =>
      exact (ordinaryCacheCouples_pure ()).bind fun _ =>
        ordinaryCacheCouples_publicAction parameter input publicState plan.action
  | some candidate =>
      exact (ordinaryCacheCouples_probe candidate).bind fun _ =>
        ordinaryCacheCouples_publicAction parameter input publicState plan.action

theorem probingHashQueryAfterRootAwarePublicPlan_probeBound
    (parameter : PublicParameter) (input : HashInput)
    (publicState : LazyRevealProbe.State Coordinate) (plan : PlannedHashQuery)
    (cache : SplitHashCache) :
    OracleComp.IsQueryBoundP
      ((probingHashQueryAfterRootAwarePublicPlan parameter input publicState plan).run cache)
      (LazyRevealProbe.IsProbe (Coordinate := Coordinate)) 1 := by
  unfold probingHashQueryAfterRootAwarePublicPlan
  rw [StateT.run_bind]
  cases hcandidate : rootAwareCandidateForPlan? parameter input plan with
  | none =>
      simp only [executeCandidate?, StateT.run_pure]
      exact OracleComp.isQueryBoundP_bind (n := 0) (m := 1) (by simp)
        (fun result _ =>
          (probingHashQueryPublicAction_probeFree parameter input publicState plan.action
            result.2).mono (by omega))
  | some candidate =>
      simp only [executeCandidate?]
      exact OracleComp.isQueryBoundP_bind (n := 1) (m := 0)
        (probe_run_isProbeBound candidate cache)
        (fun result _ =>
          probingHashQueryPublicAction_probeFree parameter input publicState plan.action result.2)

theorem relTriple_runObservedCleanFromTable_rootAwarePublicPlan_ordinaryCache
    (parameter : PublicParameter) (input : HashInput)
    (publicState state : LazyRevealProbe.State Coordinate) (plan : PlannedHashQuery)
    (leftPrefix rightPrefix : List CleanProbeObservation) (fuel : Nat)
    (table : OtsSecretIndex → HashOutput) (leftCache rightCache : SplitHashCache)
    (hcache : ordinaryQueryCache leftCache = ordinaryQueryCache rightCache) :
    RelTriple
      (runObservedCleanFromTable leftPrefix state fuel table
        ((probingHashQueryAfterRootAwarePublicPlan parameter input publicState plan).run
          leftCache))
      (runObservedCleanFromTable rightPrefix state fuel table
        ((probingHashQueryAfterRootAwarePublicPlan parameter input publicState plan).run
          rightCache))
      (ObservedOrdinaryCacheRel leftPrefix rightPrefix) := by
  let computation := probingHashQueryAfterRootAwarePublicPlan parameter input publicState plan
  have hclean := ordinaryCacheCouples_rootAwarePublicPlan parameter input publicState plan
    leftCache rightCache hcache state fuel table
  have hstrength : RelTriple
      (runCleanFromTable state fuel table (computation.run leftCache))
      (runCleanFromTable state fuel table (computation.run rightCache))
      (fun left right => ObservedOrdinaryCacheRel leftPrefix rightPrefix
        (attachCleanProbeObservations
          (observationsAfterCandidate leftPrefix state
            (rootAwareCandidateForPlan? parameter input plan)) left)
        (attachCleanProbeObservations
          (observationsAfterCandidate rightPrefix state
            (rootAwareCandidateForPlan? parameter input plan)) right)) := by
    apply relTriple_post_mono hclean
    intro left right hrelation
    cases left with
    | none =>
        cases right with
        | none => trivial
        | some right => simp [OrdinaryCacheCleanSameRel] at hrelation
    | some left =>
        cases right with
        | none => simp [OrdinaryCacheCleanSameRel] at hrelation
        | some right =>
            rcases hrelation with ⟨hstate, hremaining, htable, hvalue, hcache⟩
            refine ⟨hstate, hremaining, htable, hvalue, hcache, ?_⟩
            cases hcandidate : rootAwareCandidateForPlan? parameter input plan with
            | none =>
                exact ⟨[], by simp [observationsAfterCandidate],
                  by simp [observationsAfterCandidate]⟩
            | some candidate =>
                let observation := cleanProbeObservation state candidate.coordinate
                  candidate.candidate
                exact ⟨[observation], by
                  simp [observationsAfterCandidate, observation], by
                  simp [observationsAfterCandidate, observation]⟩
  have hmapped := relTriple_map
    (f := attachCleanProbeObservations
      (observationsAfterCandidate leftPrefix state
        (rootAwareCandidateForPlan? parameter input plan)))
    (g := attachCleanProbeObservations
      (observationsAfterCandidate rightPrefix state
        (rootAwareCandidateForPlan? parameter input plan))) hstrength
  have hpost : RelTriple
      (attachCleanProbeObservations
          (observationsAfterCandidate leftPrefix state
            (rootAwareCandidateForPlan? parameter input plan)) <$>
        runCleanFromTable state fuel table (computation.run leftCache))
      (attachCleanProbeObservations
          (observationsAfterCandidate rightPrefix state
            (rootAwareCandidateForPlan? parameter input plan)) <$>
        runCleanFromTable state fuel table (computation.run rightCache))
      (ObservedOrdinaryCacheRel leftPrefix rightPrefix) := by
    exact hmapped
  unfold computation at hpost
  rw [map_attach_runClean_rootAwarePublic_eq_observed parameter input publicState plan
      leftPrefix state fuel table leftCache,
    map_attach_runClean_rootAwarePublic_eq_observed parameter input publicState plan
      rightPrefix state fuel table rightCache] at hpost
  exact hpost

set_option maxHeartbeats 4000000 in
set_option maxRecDepth 100000 in
theorem relTriple_observedMaterializedBoundary_ordinaryCache
    (parameter : PublicParameter) (root : Digest)
    (ftsSecret : Index → FtsTree → FtsLeaf → Digest)
    (computation : OracleComp (OracleWorld + SigningSpec) α)
    (leftPrefix rightPrefix : List CleanProbeObservation)
    (state : LazyRevealProbe.State Coordinate) (fuel : Nat)
    (table : OtsSecretIndex → HashOutput) (leftCache rightCache : SplitHashCache)
    (hcache : ordinaryQueryCache leftCache = ordinaryQueryCache rightCache) :
    RelTriple
      (observedMaterializedBoundary parameter root ftsSecret computation leftPrefix state
        fuel table leftCache)
      (observedMaterializedBoundary parameter root ftsSecret computation rightPrefix state
        fuel table rightCache)
      (ObservedOrdinaryCacheRel leftPrefix rightPrefix) := by
  induction computation using OracleComp.inductionOn generalizing
      leftPrefix rightPrefix state fuel leftCache rightCache with
  | pure value =>
      rw [observedMaterializedBoundary, OracleComp.construct_pure,
        observedMaterializedBoundary, OracleComp.construct_pure]
      apply relTriple_pure_pure
      exact ⟨rfl, rfl, rfl, rfl, hcache, [], by simp, by simp⟩
  | query_bind query next ih =>
      rw [observedMaterializedBoundary, OracleComp.construct_query_bind,
        observedMaterializedBoundary, OracleComp.construct_query_bind]
      have continueAfter
          (leftRun rightRun : ProbComp (Option (ObservedCleanRunResult
            ((OracleWorld + SigningSpec).Range query × SplitHashCache))))
          (hrun : RelTriple leftRun rightRun
            (ObservedOrdinaryCacheRel leftPrefix rightPrefix)) :
          RelTriple
            (leftRun >>= fun result =>
              match result with
              | none => pure none
              | some result =>
                  observedMaterializedBoundary parameter root ftsSecret
                    (next result.value.1) result.observations result.state result.remaining table
                    result.value.2)
            (rightRun >>= fun result =>
              match result with
              | none => pure none
              | some result =>
                  observedMaterializedBoundary parameter root ftsSecret
                    (next result.value.1) result.observations result.state result.remaining table
                    result.value.2)
            (ObservedOrdinaryCacheRel leftPrefix rightPrefix) := by
        apply relTriple_bind hrun
        intro leftResult rightResult hresult
        cases leftResult with
        | none =>
            cases rightResult with
            | none => exact relTriple_pure_pure trivial
            | some rightResult => simp [ObservedOrdinaryCacheRel] at hresult
        | some leftResult =>
            cases rightResult with
            | none => simp [ObservedOrdinaryCacheRel] at hresult
            | some rightResult =>
                rcases hresult with ⟨hstate, hremaining, _htable, hvalue, hnextCache,
                  suffix, hleftObservations, hrightObservations⟩
                simp only
                rw [← hstate, ← hremaining, ← hvalue]
                have hnext := ih leftResult.value.1 leftResult.observations
                  rightResult.observations leftResult.state leftResult.remaining
                  leftResult.value.2 rightResult.value.2 hnextCache
                apply relTriple_post_mono hnext
                intro laterLeft laterRight hlater
                cases laterLeft with
                | none =>
                    cases laterRight with
                    | none => trivial
                    | some laterRight => simp [ObservedOrdinaryCacheRel] at hlater
                | some laterLeft =>
                    cases laterRight with
                    | none => simp [ObservedOrdinaryCacheRel] at hlater
                    | some laterRight =>
                        rcases hlater with ⟨hlaterState, hlaterRemaining, hlaterTable,
                          hlaterValue, hlaterCache, laterSuffix, hlaterLeft, hlaterRight⟩
                        refine ⟨hlaterState, hlaterRemaining, hlaterTable, hlaterValue,
                          hlaterCache, suffix ++ laterSuffix, ?_, ?_⟩
                        · rw [hlaterLeft, hleftObservations, List.append_assoc]
                        · rw [hlaterRight, hrightObservations, List.append_assoc]
      cases query with
      | inl worldQuery =>
          cases worldQuery with
          | inl n =>
              change Fin (n + 1) → OracleComp (OracleWorld + SigningSpec) α at next
              simp only
              have hstep :=
                relTriple_runObservedCleanFromTable_of_ordinaryCacheCouples_probeFree
                  (splitUniformImpl n) (ordinaryCacheCouples_splitUniformImpl n)
                  (splitUniformImpl_probeFree n) leftPrefix rightPrefix state fuel table
                  leftCache rightCache hcache
              convert continueAfter _ _ hstep using 1 <;>
                simp only [observedMaterializedBoundary] <;>
                apply bind_congr <;> intro result <;> cases result <;> rfl
          | inr input =>
              change HashOutput → OracleComp (OracleWorld + SigningSpec) α at next
              simp only
              let publicState :=
                (materializedCanonicalContext table state).state
              let plan := purePlanProbingHashQuery parameter input publicState
              have hstep :=
                relTriple_runObservedCleanFromTable_rootAwarePublicPlan_ordinaryCache
                  parameter input publicState state plan leftPrefix rightPrefix fuel table
                  leftCache rightCache hcache
              convert continueAfter _ _ hstep using 1 <;>
                simp only [publicState, plan, observedMaterializedBoundary] <;>
                apply bind_congr <;> intro result <;> cases result <;> rfl
      | inr message =>
          change Option Signature → OracleComp (OracleWorld + SigningSpec) α at next
          simp only
          have hstep :=
            relTriple_runObservedCleanFromTable_of_ordinaryCacheCouples_probeFree
              (maskedSign parameter root ftsSecret message)
              (ordinaryCacheCouples_maskedSign parameter root ftsSecret message)
              (maskedSign_probeFree parameter root ftsSecret message)
              leftPrefix rightPrefix state fuel table leftCache rightCache hcache
          convert continueAfter _ _ hstep using 1 <;>
            simp only [observedMaterializedBoundary] <;>
            apply bind_congr <;> intro result <;> cases result <;> rfl

theorem mem_support_runRaw_done_of_mem_runObservedCleanFromTable_some_of_probeFree
    (computation : OracleComp (LazyRevealProbe.World Coordinate) α)
    (observations : List CleanProbeObservation)
    (state : LazyRevealProbe.State Coordinate) (fuel : Nat)
    (table : OtsSecretIndex → HashOutput) (result : ObservedCleanRunResult α)
    (hprobeFree : computation.IsQueryBoundP LazyRevealProbe.IsProbe 0)
    (hresult : some result ∈ support
      (runObservedCleanFromTable observations state fuel table computation)) :
    LazyRevealProbe.RawResult.done result.state result.remaining result.value ∈
      support (LazyRevealProbe.runRaw state fuel computation) := by
  rw [← map_attachCleanProbeObservations_runCleanFromTable_of_probeFree computation
    observations state fuel table hprobeFree, support_map] at hresult
  obtain ⟨clean?, hclean, hresult⟩ := hresult
  cases clean? with
  | none => simp [attachCleanProbeObservations] at hresult
  | some clean =>
      simp [attachCleanProbeObservations] at hresult
      subst result
      exact mem_support_runRaw_done_of_mem_runCleanFromTable_some computation state fuel table
        clean hclean

set_option maxHeartbeats 4000000 in
set_option maxRecDepth 100000 in
theorem relTriple_observedMaterializedBoundary_fuel_of_isQueryBoundP
    (parameter : PublicParameter) (root : Digest)
    (ftsSecret : Index → FtsTree → FtsLeaf → Digest)
    (computation : OracleComp (OracleWorld + SigningSpec) α)
    (observations : List CleanProbeObservation)
    (state : LazyRevealProbe.State Coordinate) (leftFuel rightFuel bound : Nat)
    (table : OtsSecretIndex → HashOutput) (cache : SplitHashCache)
    (hbound :
      (simulateQ
        (SphincsSecurity.expandedAdversaryImpl
          (⟨parameter, root, tableOtsSecret (extendStartTable table), ftsSecret⟩ :
            SecretKey)) computation).IsQueryBoundP
        (fun query => query matches Sum.inr _) bound)
    (hagrees : StartTableAgrees state table)
    (hleftFuel : bound ≤ leftFuel) (hrightFuel : bound ≤ rightFuel) :
    RelTriple
      (observedMaterializedBoundary parameter root ftsSecret computation observations state
        leftFuel table cache)
      (observedMaterializedBoundary parameter root ftsSecret computation observations state
        rightFuel table cache)
      ObservedFuelRel := by
  induction computation using OracleComp.inductionOn generalizing
      observations state leftFuel rightFuel bound cache with
  | pure value =>
      rw [observedMaterializedBoundary, OracleComp.construct_pure,
        observedMaterializedBoundary, OracleComp.construct_pure]
      exact relTriple_pure_pure ⟨rfl, rfl, rfl, rfl⟩
  | query_bind query next ih =>
      rw [observedMaterializedBoundary, OracleComp.construct_query_bind,
        observedMaterializedBoundary, OracleComp.construct_query_bind]
      have continueAfter
          (step : OracleComp (LazyRevealProbe.World Coordinate)
            ((OracleWorld + SigningSpec).Range query × SplitHashCache))
          (stepCost tailBound : Nat)
          (hstepBound : step.IsQueryBoundP LazyRevealProbe.IsProbe stepCost)
          (htailBound : ∀ result,
            some result ∈ support
              (runObservedCleanFromTable observations state leftFuel table step) →
            (simulateQ
              (SphincsSecurity.expandedAdversaryImpl
                (⟨parameter, root, tableOtsSecret (extendStartTable table), ftsSecret⟩ :
                  SecretKey))
              (next result.value.1)).IsQueryBoundP
                (fun query => query matches Sum.inr _) tailBound)
          (hleftTotal : stepCost + tailBound ≤ leftFuel)
          (hrightTotal : stepCost + tailBound ≤ rightFuel) :
          RelTriple
            (runObservedCleanFromTable observations state leftFuel table step >>= fun result =>
              match result with
              | none => pure none
              | some result =>
                  observedMaterializedBoundary parameter root ftsSecret
                    (next result.value.1) result.observations result.state result.remaining table
                    result.value.2)
            (runObservedCleanFromTable observations state rightFuel table step >>= fun result =>
              match result with
              | none => pure none
              | some result =>
                  observedMaterializedBoundary parameter root ftsSecret
                    (next result.value.1) result.observations result.state result.remaining table
                    result.value.2)
            ObservedFuelRel := by
        have hstep := relTriple_runObservedCleanFromTable_fuel_of_isQueryBoundP step
          observations state leftFuel rightFuel stepCost table hstepBound
          (by omega) (by omega)
        have hleftSupported :=
          SphincsSecurity.Concrete.FtsProbeSimulation.relTriple_and_left_support hstep
            (fun result => result ∈ support
              (runObservedCleanFromTable observations state leftFuel table step))
            (fun result hresult => hresult)
        have hbothSupported :=
          SphincsSecurity.Concrete.FtsProbeSimulation.relTriple_and_right_support hleftSupported
        apply relTriple_bind hbothSupported
        intro leftResult rightResult hresult
        rcases hresult with ⟨⟨hrelation, hleftSupport⟩, hrightSupport⟩
        cases leftResult with
        | none =>
            cases rightResult with
            | none => exact relTriple_pure_pure trivial
            | some rightResult => simp [ObservedFuelRel] at hrelation
        | some leftResult =>
            cases rightResult with
            | none => simp [ObservedFuelRel] at hrelation
            | some rightResult =>
                rcases hrelation with ⟨hstate, _htable, hvalue, hobservations⟩
                have hleftRemaining := fuel_le_remaining_add_of_mem_runObservedCleanFromTable
                  step observations state leftFuel table leftResult stepCost hstepBound hleftSupport
                have hrightRemaining := fuel_le_remaining_add_of_mem_runObservedCleanFromTable
                  step observations state rightFuel table rightResult stepCost hstepBound
                  hrightSupport
                simp only
                rw [← hstate, ← hvalue, ← hobservations]
                have hnextAgrees := startTableAgrees_of_mem_runObservedCleanFromTable
                  step observations state leftFuel table hagrees leftResult hleftSupport
                exact ih leftResult.value.1 leftResult.observations leftResult.state
                  leftResult.remaining rightResult.remaining tailBound leftResult.value.2
                  (htailBound leftResult hleftSupport) hnextAgrees.2 (by omega) (by omega)
      cases query with
      | inl worldQuery =>
          cases worldQuery with
          | inl n =>
              rw [simulateQ_expandedAdversaryImpl_query_bind_inl,
                OracleComp.isQueryBoundP_query_bind_iff] at hbound
              change Fin (n + 1) → OracleComp (OracleWorld + SigningSpec) α at next
              simp only
              have htail : ∀ result,
                  some result ∈ support
                    (runObservedCleanFromTable observations state leftFuel table
                      ((splitUniformImpl n).run cache)) →
                  (simulateQ
                    (SphincsSecurity.expandedAdversaryImpl
                      (⟨parameter, root, tableOtsSecret (extendStartTable table), ftsSecret⟩ :
                        SecretKey))
                    (next result.value.1)).IsQueryBoundP
                      (fun query => query matches Sum.inr _) bound := by
                intro result _hresult
                exact hbound.2 result.value.1
              have hrun := continueAfter ((splitUniformImpl n).run cache) 0 bound
                (splitUniformImpl_probeFree n cache) htail (by omega) (by omega)
              convert hrun using 1 <;>
                simp only [observedMaterializedBoundary] <;>
                apply bind_congr <;> intro result <;> cases result <;> rfl
          | inr input =>
              rw [simulateQ_expandedAdversaryImpl_query_bind_inl,
                OracleComp.isQueryBoundP_query_bind_iff] at hbound
              change HashOutput → OracleComp (OracleWorld + SigningSpec) α at next
              simp only
              have hpositive : 0 < bound := by
                rcases hbound.1 with hnot | hpositive
                · exact (hnot (by simp)).elim
                · exact hpositive
              let publicState := (materializedCanonicalContext table state).state
              let plan := purePlanProbingHashQuery parameter input publicState
              let step :=
                (probingHashQueryAfterRootAwarePublicPlan parameter input publicState plan).run
                  cache
              have htail : ∀ result,
                  some result ∈ support
                    (runObservedCleanFromTable observations state leftFuel table step) →
                  (simulateQ
                    (SphincsSecurity.expandedAdversaryImpl
                      (⟨parameter, root, tableOtsSecret (extendStartTable table), ftsSecret⟩ :
                        SecretKey))
                    (next result.value.1)).IsQueryBoundP
                      (fun query => query matches Sum.inr _) (bound - 1) := by
                intro result _hresult
                exact hbound.2 result.value.1
              have hrun := continueAfter step 1 (bound - 1)
                (probingHashQueryAfterRootAwarePublicPlan_probeBound parameter input publicState
                  plan cache)
                htail (by omega) (by omega)
              convert hrun using 1 <;>
                simp only [step, publicState, plan, observedMaterializedBoundary] <;>
                apply bind_congr <;> intro result <;> cases result <;> rfl
      | inr message =>
          rw [simulateQ_expandedAdversaryImpl_query_bind_inr] at hbound
          change Option Signature → OracleComp (OracleWorld + SigningSpec) α at next
          simp only
          have htail : ∀ result,
              some result ∈ support
                (runObservedCleanFromTable observations state leftFuel table
                  ((maskedSign parameter root ftsSecret message).run cache)) →
              (simulateQ
                (SphincsSecurity.expandedAdversaryImpl
                  (⟨parameter, root, tableOtsSecret (extendStartTable table), ftsSecret⟩ :
                    SecretKey))
                (next result.value.1)).IsQueryBoundP
                  (fun query => query matches Sum.inr _) bound := by
            intro result hresult
            have hnextAgrees := startTableAgrees_of_mem_runObservedCleanFromTable
              ((maskedSign parameter root ftsSecret message).run cache) observations state
              leftFuel table hagrees result hresult
            have hraw :=
              mem_support_runRaw_done_of_mem_runObservedCleanFromTable_some_of_probeFree
                ((maskedSign parameter root ftsSecret message).run cache) observations state
                leftFuel table result
                (maskedSign_probeFree parameter root ftsSecret message cache) hresult
            have houtput : result.value.1 ∈ support
                (scheme.sign
                  (⟨parameter, root, tableOtsSecret (extendStartTable table), ftsSecret⟩ :
                    SecretKey) message) := by
              exact maskedSign_done_output_mem_support parameter root table ftsSecret message
                state result.state cache result.value.2 leftFuel result.remaining result.value.1
                hnextAgrees.2 hraw
            exact isQueryBoundP_of_bind hbound result.value.1 houtput
          have hrun := continueAfter ((maskedSign parameter root ftsSecret message).run cache)
            0 bound (maskedSign_probeFree parameter root ftsSecret message cache) htail
            (by omega) (by omega)
          convert hrun using 1 <;>
            simp only [observedMaterializedBoundary] <;>
            apply bind_congr <;> intro result <;> cases result <;> rfl

theorem exists_finishObservedCleanRunFromTable_of_state_table_eq
    (left right : ObservedCleanRunResult α)
    (hstate : left.state = right.state) (htable : left.table = right.table)
    (hleft : ∃ finalResult, some finalResult ∈ support
      (finishObservedCleanRunFromTable (some left))) :
    ∃ finalResult, some finalResult ∈ support
      (finishObservedCleanRunFromTable (some right)) := by
  obtain ⟨leftFinal, hleftFinal⟩ := hleft
  unfold finishObservedCleanRunFromTable at hleftFinal ⊢
  simp only at hleftFinal ⊢
  rw [mem_support_bind_iff] at hleftFinal
  obtain ⟨finalized, hfinalized, hreturn⟩ := hleftFinal
  cases finalized with
  | none => simp at hreturn
  | some finalized =>
      rcases finalized with ⟨finalState, finalTable⟩
      refine ⟨⟨finalState, right.remaining, right.value, finalTable,
        right.observations⟩, ?_⟩
      rw [mem_support_bind_iff]
      refine ⟨some (finalState, finalTable), ?_, by simp⟩
      simpa [← hstate, ← htable] using hfinalized

theorem ObservedOrdinaryCacheRel.successfulDoomedFirstRootGoodForComparisonAt
    (table : OtsSecretIndex → HashOutput) (ordinal : Nat)
    (target : Position) (rightRoot : Digest)
    (leftPrefix rightPrefix : List CleanProbeObservation)
    (hordinal : leftPrefix.length = ordinal)
    (hprobes : leftPrefix.map CleanProbeObservation.toProbe =
      rightPrefix.map CleanProbeObservation.toProbe)
    (_hleftNoHit : ∀ observation ∈ leftPrefix, ¬observation.ExistingHiddenHit)
    (hrightNoHit : ∀ observation ∈ rightPrefix, ¬observation.ExistingHiddenHit)
    (left right : ObservedCleanRunResult (α × SplitHashCache))
    (hrel : ObservedOrdinaryCacheRel leftPrefix rightPrefix (some left) (some right))
    (hgood : ObservedCleanRunOption.SuccessfulDoomedFirstRootGoodForComparisonAt
      table ordinal target rightRoot (some left)) :
    ObservedCleanRunOption.SuccessfulDoomedFirstRootGoodForComparisonAt
      table ordinal target rightRoot (some right) := by
  rcases hrel with ⟨hstate, _hremaining, htable, _hvalue, _hcache,
    suffix, hleftObservations, hrightObservations⟩
  have hprefixLength : leftPrefix.length = rightPrefix.length := by
    simpa using congrArg List.length hprobes
  have hrightOrdinal : rightPrefix.length = ordinal := hprefixLength.symm.trans hordinal
  have hobservationLength : left.observations.length = right.observations.length := by
    rw [hleftObservations, hrightObservations, List.length_append, List.length_append,
      hprefixLength]
  rcases hgood with ⟨hhitTarget, hcomparison⟩
  rcases hhitTarget with ⟨hsuccessful, hposition⟩
  rcases hsuccessful with ⟨hfinish, hdoomed, hfirstRoot⟩
  rcases hfirstRoot with ⟨selected, hselected, hfirst, hroot⟩
  have hrightSelectedLt : ordinal < right.observations.length := by
    rw [← hobservationLength, ← hselected]
    exact selected.isLt
  have hleftSelectedLt : ordinal < left.observations.length := by
    rw [hobservationLength]
    exact hrightSelectedLt
  let leftSelected : Fin left.observations.length := ⟨ordinal, hleftSelectedLt⟩
  let rightSelected : Fin right.observations.length := ⟨ordinal, hrightSelectedLt⟩
  have hselectedEq : selected = leftSelected := Fin.ext hselected
  have hobservationEq : left.observations.get leftSelected =
      right.observations.get rightSelected := by
    simp [leftSelected, rightSelected, hleftObservations, hrightObservations,
      hordinal, hrightOrdinal]
  rcases hfirst with ⟨first, hfirstOrdinal, hfirstHit, _hbefore⟩
  have hfirstEq : first = leftSelected := Fin.ext hfirstOrdinal
  subst first
  have hrightFirst : FirstExistingHiddenHitAt right ordinal := by
    refine ⟨rightSelected, rfl, ?_, ?_⟩
    · rw [ExistingHiddenHitAtOrdinal, ← hobservationEq]
      exact hfirstHit
    · intro earlier hearlier
      have hearlierPrefix : earlier.val < rightPrefix.length := by
        rw [hrightOrdinal]
        exact hearlier
      let before : Fin rightPrefix.length := ⟨earlier.val, hearlierPrefix⟩
      have hobservation : right.observations.get earlier = rightPrefix.get before := by
        simp [before, hrightObservations, hearlierPrefix]
      rw [ExistingHiddenHitAtOrdinal, hobservation]
      exact hrightNoHit (rightPrefix.get before) (List.get_mem _ _)
  have hrightRoot :
      (right.observations.get rightSelected).toProbe.IsLayerRoot := by
    rw [← hobservationEq]
    rw [← hselectedEq]
    exact hroot
  have hrightFirstRoot :
      ObservedCleanRunOption.FirstExistingHiddenRootHitAt ordinal (some right) :=
    ⟨rightSelected, rfl, hrightFirst, hrightRoot⟩
  have hrightPosition :
      observedFirstLayerRootPosition? ordinal (some right) = some target := by
    unfold observedFirstLayerRootPosition? at hposition ⊢
    simp only [hrightSelectedLt, ↓reduceDIte]
    simp only [hleftSelectedLt, ↓reduceDIte] at hposition
    change candidateLayerRootPosition? (right.observations.get rightSelected).toProbe =
      some target
    rw [← hobservationEq]
    exact hposition
  have hrightComparison : CandidatesAvoidRoot target rightRoot
      (observedPrefixProbes ordinal (some right)) := by
    have hleftTake : left.observations.take ordinal = leftPrefix := by
      rw [hleftObservations, ← hordinal,
        List.take_append_of_le_length (Nat.le_refl _),
        List.take_length]
    have hrightTake : right.observations.take ordinal = rightPrefix := by
      rw [hrightObservations, ← hrightOrdinal,
        List.take_append_of_le_length (Nat.le_refl _),
        List.take_length]
    simpa [observedPrefixProbes, hleftTake, hrightTake, hprobes] using hcomparison
  have hrightFinish := exists_finishObservedCleanRunFromTable_of_state_table_eq
    left right hstate htable hfinish
  have hrightDoomed :
      ¬DeferredCompletable table (directDeferredContext right.state) := by
    rw [← hstate]
    exact hdoomed
  exact ⟨⟨⟨hrightFinish, hrightDoomed, hrightFirstRoot⟩,
    hrightPosition⟩, hrightComparison⟩

theorem ObservedFuelRel.successfulDoomedFirstRootGoodForComparisonAt
    (table : OtsSecretIndex → HashOutput) (ordinal : Nat)
    (target : Position) (rightRoot : Digest)
    (left right : ObservedCleanRunResult (α × SplitHashCache))
    (hrel : ObservedFuelRel (some left) (some right))
    (hgood : ObservedCleanRunOption.SuccessfulDoomedFirstRootGoodForComparisonAt
      table ordinal target rightRoot (some left)) :
    ObservedCleanRunOption.SuccessfulDoomedFirstRootGoodForComparisonAt
      table ordinal target rightRoot (some right) := by
  rcases hrel with ⟨hstate, htable, _hvalue, hobservations⟩
  rcases hgood with
    ⟨⟨⟨hfinish, hdoomed, hfirstRoot⟩, hposition⟩, hcomparison⟩
  have hrightFinish := exists_finishObservedCleanRunFromTable_of_state_table_eq
    left right hstate htable hfinish
  have hrightDoomed :
      ¬DeferredCompletable table (directDeferredContext right.state) := by
    rw [← hstate]
    exact hdoomed
  have hrightPosition :
      observedFirstLayerRootPosition? ordinal (some right) = some target := by
    rw [← observedFirstLayerRootPosition?_eq_of_observations_eq ordinal left right
      hobservations]
    exact hposition
  obtain ⟨_selected, _hselected, hfirst, _hroot⟩ := hfirstRoot
  have hrightFirst := firstExistingHiddenHitAt_of_observations_eq left right ordinal
    hobservations hfirst
  have hrightFirstRoot :
      ObservedCleanRunOption.FirstExistingHiddenRootHitAt ordinal (some right) :=
    firstExistingHiddenRootHitAt_of_first_of_position right ordinal target hrightFirst
      hrightPosition
  have hrightComparison : CandidatesAvoidRoot target rightRoot
      (observedPrefixProbes ordinal (some right)) := by
    rw [← observedPrefixProbes_eq_of_observations_eq ordinal left right hobservations]
    exact hcomparison
  exact ⟨⟨⟨hrightFinish, hrightDoomed, hrightFirstRoot⟩,
    hrightPosition⟩, hrightComparison⟩

set_option maxHeartbeats 4000000 in
set_option maxRecDepth 100000 in
theorem relTriple_indicator_observedMaterializedBoundary_ordinaryCache
    (ordinal : Nat) (parameter : PublicParameter) (publicRoot rightRoot : Digest)
    (ftsSecret : Index → FtsTree → FtsLeaf → Digest)
    (table : OtsSecretIndex → HashOutput) (target : Position)
    (computation : OracleComp (OracleWorld + SigningSpec) α)
    (leftPrefix rightPrefix : List CleanProbeObservation)
    (state : LazyRevealProbe.State Coordinate) (fuel : Nat)
    (leftCache rightCache : SplitHashCache)
    (hcache : ordinaryQueryCache leftCache = ordinaryQueryCache rightCache)
    (hordinal : leftPrefix.length = ordinal)
    (hprobes : leftPrefix.map CleanProbeObservation.toProbe =
      rightPrefix.map CleanProbeObservation.toProbe)
    (hleftNoHit : ∀ observation ∈ leftPrefix, ¬observation.ExistingHiddenHit)
    (hrightNoHit : ∀ observation ∈ rightPrefix, ¬observation.ExistingHiddenHit) :
    RelTriple
      ((successfulObservedRootComparisonIndicator table ordinal target ∘
          fun observed ↦ (observed, rightRoot)) <$>
        observedMaterializedBoundary parameter publicRoot ftsSecret computation leftPrefix state
          fuel table leftCache)
      ((successfulObservedRootComparisonIndicator table ordinal target ∘
          fun observed ↦ (observed, rightRoot)) <$>
        observedMaterializedBoundary parameter publicRoot ftsSecret computation rightPrefix state
          fuel table rightCache)
      SuccessfulObservedIndicatorRel := by
  apply relTriple_map
  apply relTriple_post_mono
    (relTriple_observedMaterializedBoundary_ordinaryCache parameter publicRoot ftsSecret
      computation leftPrefix rightPrefix state fuel table leftCache rightCache hcache)
  intro leftResult rightResult hrelation hleftGood
  change successfulObservedRootComparisonIndicator table ordinal target
    (leftResult, rightRoot) = true at hleftGood
  rw [successfulObservedRootComparisonIndicator_eq_true_iff] at hleftGood
  change successfulObservedRootComparisonIndicator table ordinal target
    (rightResult, rightRoot) = true
  rw [successfulObservedRootComparisonIndicator_eq_true_iff]
  cases leftResult with
  | none =>
      simp [ObservedCleanRunOption.SuccessfulDoomedFirstRootGoodForComparisonAt,
        ObservedCleanRunOption.SuccessfulDoomedFirstRootHitAtTarget,
        ObservedCleanRunOption.SuccessfulDoomedFirstExistingHiddenRootHitAt] at hleftGood
  | some leftResult =>
      cases rightResult with
      | none => simp [ObservedOrdinaryCacheRel] at hrelation
      | some rightResult =>
          exact hrelation.successfulDoomedFirstRootGoodForComparisonAt table ordinal target
            rightRoot leftPrefix rightPrefix hordinal hprobes hleftNoHit hrightNoHit
            leftResult rightResult hleftGood

set_option maxHeartbeats 4000000 in
set_option maxRecDepth 100000 in
theorem relTriple_indicator_observedMaterializedBoundary_fuel_of_isQueryBoundP
    (ordinal : Nat) (parameter : PublicParameter) (publicRoot rightRoot : Digest)
    (ftsSecret : Index → FtsTree → FtsLeaf → Digest)
    (table : OtsSecretIndex → HashOutput) (target : Position)
    (computation : OracleComp (OracleWorld + SigningSpec) α)
    (observations : List CleanProbeObservation)
    (state : LazyRevealProbe.State Coordinate) (leftFuel rightFuel bound : Nat)
    (cache : SplitHashCache)
    (hbound :
      (simulateQ
        (SphincsSecurity.expandedAdversaryImpl
          (⟨parameter, publicRoot, tableOtsSecret (extendStartTable table), ftsSecret⟩ :
            SecretKey)) computation).IsQueryBoundP
        (fun query => query matches Sum.inr _) bound)
    (hagrees : StartTableAgrees state table)
    (hleftFuel : bound ≤ leftFuel) (hrightFuel : bound ≤ rightFuel) :
    RelTriple
      ((successfulObservedRootComparisonIndicator table ordinal target ∘
          fun observed ↦ (observed, rightRoot)) <$>
        observedMaterializedBoundary parameter publicRoot ftsSecret computation observations state
          leftFuel table cache)
      ((successfulObservedRootComparisonIndicator table ordinal target ∘
          fun observed ↦ (observed, rightRoot)) <$>
        observedMaterializedBoundary parameter publicRoot ftsSecret computation observations state
          rightFuel table cache)
      SuccessfulObservedIndicatorRel := by
  apply relTriple_map
  apply relTriple_post_mono
    (relTriple_observedMaterializedBoundary_fuel_of_isQueryBoundP parameter publicRoot ftsSecret
      computation observations state leftFuel rightFuel bound table cache hbound hagrees
      hleftFuel hrightFuel)
  intro leftResult rightResult hrelation hleftGood
  change successfulObservedRootComparisonIndicator table ordinal target
    (leftResult, rightRoot) = true at hleftGood
  rw [successfulObservedRootComparisonIndicator_eq_true_iff] at hleftGood
  change successfulObservedRootComparisonIndicator table ordinal target
    (rightResult, rightRoot) = true
  rw [successfulObservedRootComparisonIndicator_eq_true_iff]
  cases leftResult with
  | none =>
      simp [ObservedCleanRunOption.SuccessfulDoomedFirstRootGoodForComparisonAt,
        ObservedCleanRunOption.SuccessfulDoomedFirstRootHitAtTarget,
        ObservedCleanRunOption.SuccessfulDoomedFirstExistingHiddenRootHitAt] at hleftGood
  | some leftResult =>
      cases rightResult with
      | none => simp [ObservedFuelRel] at hrelation
      | some rightResult =>
          exact hrelation.successfulDoomedFirstRootGoodForComparisonAt table ordinal target
            rightRoot leftResult rightResult hleftGood

end SphincsSecurity.Concrete.OtsProbeSimulation
