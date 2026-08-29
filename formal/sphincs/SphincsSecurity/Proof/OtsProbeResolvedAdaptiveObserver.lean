import SphincsSecurity.Proof.OtsProbeResolvedPrivateSigner

namespace SphincsSecurity.Concrete.OtsProbeSimulation

open OracleComp

attribute [local irreducible] maskedSignLayer

def ResolvedPreservesCoordinate (coordinate : Coordinate)
    (computation : StateT SplitHashCache
      (OracleComp (LazyRevealProbe.World Coordinate)) α) : Prop :=
  ∀ context fuel table cache result,
    some result ∈ support
      (runResolvedFromTable context fuel table (computation.run cache)) →
    result.context.state.values coordinate = context.state.values coordinate ∧
      (coordinate ∈ result.context.state.revealed ↔
        coordinate ∈ context.state.revealed)

theorem ResolvedPreservesCoordinate.bind
    {coordinate : Coordinate}
    {left : StateT SplitHashCache
      (OracleComp (LazyRevealProbe.World Coordinate)) α}
    {next : α → StateT SplitHashCache
      (OracleComp (LazyRevealProbe.World Coordinate)) β}
    (hleft : ResolvedPreservesCoordinate coordinate left)
    (hnext : ∀ value, ResolvedPreservesCoordinate coordinate (next value)) :
    ResolvedPreservesCoordinate coordinate (left >>= next) := by
  intro context fuel table cache result hresult
  rw [StateT.run_bind, runResolvedFromTable_bind, mem_support_bind_iff] at hresult
  obtain ⟨leftOption, hleftSupport, hrest⟩ := hresult
  cases leftOption with
  | none => simp at hrest
  | some leftResult =>
      have hmiddle := hleft context fuel table cache leftResult hleftSupport
      have hfinal := hnext leftResult.value.1 leftResult.context leftResult.remaining
        leftResult.table leftResult.value.2 result hrest
      exact ⟨hfinal.1.trans hmiddle.1, hfinal.2.trans hmiddle.2⟩

theorem resolvedPreservesCoordinate_pure (coordinate : Coordinate) (value : α) :
    ResolvedPreservesCoordinate coordinate
      (pure value : StateT SplitHashCache
        (OracleComp (LazyRevealProbe.World Coordinate)) α) := by
  intro context fuel table cache result hresult
  simp [runResolvedFromTable] at hresult
  subst result
  exact ⟨rfl, Iff.rfl⟩

theorem ResolvedPreservesPublished.of_preservesCoordinate
    {computation : StateT SplitHashCache
      (OracleComp (LazyRevealProbe.World Coordinate)) α}
    (hpreserves : ∀ coordinate,
      ResolvedPreservesCoordinate coordinate computation) :
    ResolvedPreservesPublished computation := by
  intro context cache fuel table result hpublished hresult coordinate hrevealed
  have hcoordinate := hpreserves coordinate context fuel table cache result hresult
  rw [hcoordinate.1]
  exact hpublished coordinate (hcoordinate.2.mp hrevealed)

theorem resolvedPreservesCoordinate_get (coordinate : Coordinate) :
    ResolvedPreservesCoordinate coordinate
      (get : StateT SplitHashCache
        (OracleComp (LazyRevealProbe.World Coordinate)) SplitHashCache) := by
  intro context fuel table cache result hresult
  simp [runResolvedFromTable] at hresult
  subst result
  exact ⟨rfl, Iff.rfl⟩

theorem resolvedPreservesCoordinate_modify (coordinate : Coordinate)
    (update : SplitHashCache → SplitHashCache) :
    ResolvedPreservesCoordinate coordinate
      (modify update : StateT SplitHashCache
        (OracleComp (LazyRevealProbe.World Coordinate)) Unit) := by
  intro context fuel table cache result hresult
  simp [StateT.run_modify, runResolvedFromTable] at hresult
  subst result
  exact ⟨rfl, Iff.rfl⟩

theorem resolvedPreservesCoordinate_splitHashQuery
    (coordinate : Coordinate) (key : SplitHashKey) :
    ResolvedPreservesCoordinate coordinate (splitHashQuery key) := by
  intro context fuel table cache result hresult
  rw [splitHashQuery_run_eq] at hresult
  cases hlookup : cache key with
  | some output =>
      rw [hlookup] at hresult
      simp [runResolvedFromTable] at hresult
      subst result
      exact ⟨rfl, Iff.rfl⟩
  | none =>
      rw [hlookup] at hresult
      dsimp only at hresult
      change some result ∈ support (runResolvedFromTable context fuel table
        (LazyRevealProbe.hashOutputQuery >>= fun output =>
          pure (output, Function.update cache key (some output)))) at hresult
      rw [LazyRevealProbe.hashOutputQuery] at hresult
      rw [runResolvedFromTable_hashOutput_query_bind, mem_support_bind_iff] at hresult
      obtain ⟨output, _houtput, hdone⟩ := hresult
      simp [runResolvedFromTable] at hdone
      subst result
      exact ⟨rfl, Iff.rfl⟩

theorem resolvedPreservesCoordinate_ensure
    (coordinate ensured : Coordinate) :
    ResolvedPreservesCoordinate coordinate (ensureCoordinate ensured) := by
  intro context fuel table cache result hresult
  change some result ∈ support (runResolvedFromTable context fuel table
    (LazyRevealProbe.ensureQuery ensured >>= fun output => pure (output, cache))) at hresult
  rw [LazyRevealProbe.ensureQuery] at hresult
  rw [runResolvedFromTable_ensure_query_bind] at hresult
  simp [runResolvedFromTable, LazyRevealProbe.State.ensure] at hresult
  subst result
  exact ⟨rfl, Iff.rfl⟩

theorem resolvedPreservesCoordinate_probe
    (coordinate : Coordinate) (candidate : Probe) :
    ResolvedPreservesCoordinate coordinate (probe candidate) := by
  intro context fuel table cache result hresult
  change some result ∈ support (runResolvedFromTable context fuel table
    (LazyRevealProbe.probeQuery candidate.coordinate candidate.candidate >>= fun output =>
      pure (output, cache))) at hresult
  rw [LazyRevealProbe.probeQuery] at hresult
  rw [runResolvedFromTable_probe_query_bind] at hresult
  cases fuel with
  | zero => simp at hresult
  | succ remaining =>
      by_cases hrevealed : candidate.coordinate ∈ context.state.revealed
      · simp only [hrevealed, ↓reduceIte] at hresult
        simp [runResolvedFromTable] at hresult
        subst result
        exact ⟨rfl, Iff.rfl⟩
      · simp only [hrevealed, ↓reduceIte] at hresult
        change some result ∈ support (runResolvedFromTable
          { context with state :=
              (context.state.addPending candidate.coordinate candidate.candidate) }
          remaining table (pure ((), cache))) at hresult
        simp [runResolvedFromTable, LazyRevealProbe.State.addPending] at hresult
        subst result
        exact ⟨rfl, Iff.rfl⟩

theorem resolvedPreservesCoordinate_peekCoordinate
    (coordinate observed : Coordinate) :
    ResolvedPreservesCoordinate coordinate (peekCoordinate observed) := by
  intro context fuel table cache result hresult
  change some result ∈ support (runResolvedFromTable context fuel table
    (LazyRevealProbe.peekQuery observed >>= fun output =>
      pure (truncateHash <$> output, cache))) at hresult
  rw [LazyRevealProbe.peekQuery, runResolvedFromTable_peek_query_bind] at hresult
  simp [runResolvedFromTable] at hresult
  subst result
  exact ⟨rfl, Iff.rfl⟩

theorem resolvedPreservesCoordinate_peekPositionValues
    (coordinate : Coordinate) : ∀ positions,
    ResolvedPreservesCoordinate coordinate (peekPositionValues positions)
  | [] => resolvedPreservesCoordinate_pure coordinate (some [])
  | position :: remaining => by
      rw [peekPositionValues]
      exact (resolvedPreservesCoordinate_peekCoordinate coordinate (.position position)).bind
        fun value => match value with
        | none => resolvedPreservesCoordinate_pure coordinate none
        | some value =>
            (resolvedPreservesCoordinate_peekPositionValues coordinate remaining).bind
              fun values => match values with
              | none => resolvedPreservesCoordinate_pure coordinate none
              | some values => resolvedPreservesCoordinate_pure coordinate
                  (some (value :: values))

theorem resolvedPreservesCoordinate_peekTableInput
    (parameter : PublicParameter) (coordinate : Coordinate) : ∀ target,
    ResolvedPreservesCoordinate coordinate (peekTableInput parameter target)
  | .chainStart _ _ _ _ => resolvedPreservesCoordinate_pure coordinate none
  | .position position => by
      cases position with
      | chain lay tree leafIdx chainIdx step =>
          rw [peekTableInput]
          by_cases hstep : step.val = 0
          · rw [if_pos hstep]
            exact (resolvedPreservesCoordinate_peekCoordinate coordinate
              (.chainStart lay tree leafIdx chainIdx)).bind fun value => match value with
              | none => resolvedPreservesCoordinate_pure coordinate none
              | some value => resolvedPreservesCoordinate_pure coordinate
                  (some (tweakableHashInput parameter
                    (Position.chain lay tree leafIdx chainIdx step).domain
                      (digestBytes value)))
          · rw [if_neg hstep]
            exact (resolvedPreservesCoordinate_peekPositionValues coordinate
              (Position.chain lay tree leafIdx chainIdx step).children).bind
                fun values => match values with
                | none => resolvedPreservesCoordinate_pure coordinate none
                | some values => resolvedPreservesCoordinate_pure coordinate
                    (some (tweakableHashInput parameter
                      (Position.chain lay tree leafIdx chainIdx step).domain
                        (values.flatMap digestBytes)))
      | leaf lay tree leafIdx =>
          simp only [peekTableInput]
          exact (resolvedPreservesCoordinate_peekPositionValues coordinate
            (Position.leaf lay tree leafIdx).children).bind fun values => match values with
            | none => resolvedPreservesCoordinate_pure coordinate none
            | some values => resolvedPreservesCoordinate_pure coordinate
                (some (tweakableHashInput parameter (Position.leaf lay tree leafIdx).domain
                  (values.flatMap digestBytes)))
      | node lay tree level nodeIdx =>
          simp only [peekTableInput]
          exact (resolvedPreservesCoordinate_peekPositionValues coordinate
            (Position.node lay tree level nodeIdx).children).bind fun values => match values with
            | none => resolvedPreservesCoordinate_pure coordinate none
            | some values => resolvedPreservesCoordinate_pure coordinate
                (some (tweakableHashInput parameter
                  (Position.node lay tree level nodeIdx).domain
                    (values.flatMap digestBytes)))
      | ftsLeaf index tree leafIdx =>
          simp only [peekTableInput]
          exact (resolvedPreservesCoordinate_peekPositionValues coordinate
            (Position.ftsLeaf index tree leafIdx).children).bind fun values => match values with
            | none => resolvedPreservesCoordinate_pure coordinate none
            | some values => resolvedPreservesCoordinate_pure coordinate
                (some (tweakableHashInput parameter (Position.ftsLeaf index tree leafIdx).domain
                  (values.flatMap digestBytes)))
      | ftsNode index tree level nodeIdx =>
          simp only [peekTableInput]
          exact (resolvedPreservesCoordinate_peekPositionValues coordinate
            (Position.ftsNode index tree level nodeIdx).children).bind fun values => match values with
            | none => resolvedPreservesCoordinate_pure coordinate none
            | some values => resolvedPreservesCoordinate_pure coordinate
                (some (tweakableHashInput parameter
                  (Position.ftsNode index tree level nodeIdx).domain
                    (values.flatMap digestBytes)))
      | ftsRoots index =>
          simp only [peekTableInput]
          exact (resolvedPreservesCoordinate_peekPositionValues coordinate
            (Position.ftsRoots index).children).bind fun values => match values with
            | none => resolvedPreservesCoordinate_pure coordinate none
            | some values => resolvedPreservesCoordinate_pure coordinate
                (some (tweakableHashInput parameter (Position.ftsRoots index).domain
                  (values.flatMap digestBytes)))

theorem resolvedPreservesCoordinate_publish_of_ne
    (coordinate published : Coordinate) (hne : coordinate ≠ published) :
    ResolvedPreservesCoordinate coordinate (publishCoordinate published) := by
  intro context fuel table cache result hresult
  change some result ∈ support (runResolvedFromTable context fuel table
    (LazyRevealProbe.publishQuery published >>= fun output => pure (output, cache))) at hresult
  rw [LazyRevealProbe.publishQuery, runResolvedFromTable_publish_query_bind] at hresult
  simp [runResolvedFromTable] at hresult
  subst result
  simp [LazyRevealProbe.State.publish, hne]

theorem resolvedPreservesCoordinate_revealCoordinateOutput_of_ne
    (coordinate revealed : Coordinate) (hne : coordinate ≠ revealed) :
    ResolvedPreservesCoordinate coordinate (revealCoordinateOutput revealed) := by
  intro context fuel table cache result hresult
  rw [runResolvedFromTable_revealCoordinateOutput] at hresult
  cases revealed with
  | chainStart lay tree leafIdx chainIdx =>
      cases hresolve : resolveDeferredChainStart table
          ⟨lay, tree, leafIdx, chainIdx⟩ context with
      | none => simp [hresolve] at hresult
      | some resolved =>
          simp [hresolve] at hresult
          subst result
          simp [LazyRevealProbe.State.materialize, Function.update, hne]
  | position position =>
      rw [mem_support_bind_iff] at hresult
      obtain ⟨resolvedOption, _hresolved, hrest⟩ := hresult
      cases resolvedOption with
      | none => simp at hrest
      | some resolved =>
          simp at hrest
          subst result
          simp [LazyRevealProbe.State.materialize, Function.update, hne]

theorem resolvedPreservesPublishedValues_revealCoordinateOutput
    (coordinate : Coordinate) :
    ResolvedPreservesPublished (revealCoordinateOutput coordinate) := by
  intro context cache fuel table result hpublished hresult
  rw [runResolvedFromTable_revealCoordinateOutput] at hresult
  cases coordinate with
  | chainStart lay tree leafIdx chainIdx =>
      cases hresolve : resolveDeferredChainStart table
          ⟨lay, tree, leafIdx, chainIdx⟩ context with
      | none => simp [hresolve] at hresult
      | some resolved =>
          simp [hresolve] at hresult
          subst result
          intro other hother
          by_cases heq : other = .chainStart lay tree leafIdx chainIdx
          · subst other
            simp [LazyRevealProbe.State.materialize]
          · have hvalue := hpublished other (by
              simpa [LazyRevealProbe.State.materialize] using hother)
            simpa [LazyRevealProbe.State.materialize, Function.update, heq] using hvalue
  | position position =>
      rw [mem_support_bind_iff] at hresult
      obtain ⟨resolvedOption, _hresolved, hrest⟩ := hresult
      cases resolvedOption with
      | none => simp at hrest
      | some resolved =>
          simp at hrest
          subst result
          intro other hother
          by_cases heq : other = .position position
          · subst other
            simp [LazyRevealProbe.State.materialize]
          · have hvalue := hpublished other (by
              simpa [LazyRevealProbe.State.materialize] using hother)
            simpa [LazyRevealProbe.State.materialize, Function.update, heq] using hvalue

theorem resolvedPreservesPublishedValues_revealCoordinateOutput_publish
    (coordinate : Coordinate) :
    ResolvedPreservesPublished (do
      let output ← revealCoordinateOutput coordinate
      publishCoordinate coordinate
      pure output) := by
  intro context cache fuel table result hpublished hresult
  rw [StateT.run_bind, runResolvedFromTable_bind, mem_support_bind_iff] at hresult
  obtain ⟨revealOption, hreveal, hrest⟩ := hresult
  cases revealOption with
  | none => simp at hrest
  | some revealResult =>
      simp only at hrest
      rw [StateT.run_bind, runResolvedFromTable_bind, mem_support_bind_iff] at hrest
      obtain ⟨publishOption, hpublish, hreturn⟩ := hrest
      cases publishOption with
      | none => simp at hreturn
      | some publishResult =>
          simp [runResolvedFromTable] at hreturn
          subst result
          have hpublishedReveal :=
            resolvedPreservesPublishedValues_revealCoordinateOutput coordinate context cache fuel
              table revealResult hpublished hreveal
          change some publishResult ∈ support (runResolvedFromTable revealResult.context
            revealResult.remaining revealResult.table
              ((publishCoordinate coordinate).run revealResult.value.2)) at hpublish
          change some publishResult ∈ support (runResolvedFromTable revealResult.context
            revealResult.remaining revealResult.table
              (LazyRevealProbe.publishQuery coordinate >>= fun output =>
                pure (output, revealResult.value.2))) at hpublish
          rw [LazyRevealProbe.publishQuery,
            runResolvedFromTable_publish_query_bind] at hpublish
          simp [runResolvedFromTable] at hpublish
          subst publishResult
          intro other hother
          by_cases heq : other = coordinate
          · subst other
            have hvalue := value_of_mem_runResolvedFromTable_revealCoordinateOutput context fuel
              table coordinate cache revealResult hreveal
            simp [LazyRevealProbe.State.publish, hvalue]
          · have hvalue := hpublishedReveal other (by
              simpa [LazyRevealProbe.State.publish, heq] using hother)
            simpa [LazyRevealProbe.State.publish] using hvalue

theorem resolvedPreservesPublishedValues_resolveKnownInput
    (parameter : PublicParameter) (coordinate : Coordinate) (input : HashInput) :
    ResolvedPreservesPublished (resolveKnownInput parameter coordinate input) := by
  unfold resolveKnownInput
  apply (ResolvedPreservesPublished.of_preservesCoordinate fun other =>
    resolvedPreservesCoordinate_peekTableInput parameter other coordinate).bind
  intro known
  cases known with
  | none =>
      exact ResolvedPreservesPublished.of_preservesCoordinate fun other =>
        resolvedPreservesCoordinate_splitHashQuery other (.ordinary input)
  | some knownInput =>
      by_cases heq : knownInput = input
      · simp only [heq, ↓reduceIte]
        have hpreserves :=
          (resolvedPreservesPublishedValues_revealCoordinateOutput_publish coordinate).bind
            fun output =>
              (ResolvedPreservesPublished.of_preservesCoordinate fun other =>
                resolvedPreservesCoordinate_modify other fun cache =>
                  Function.update cache (.ordinary input) (some output)).bind fun _ =>
                    ResolvedPreservesPublished.pure output
        simpa only [bind_assoc, pure_bind] using hpreserves
      · simp only [heq, ↓reduceIte]
        exact ResolvedPreservesPublished.of_preservesCoordinate fun other =>
          resolvedPreservesCoordinate_splitHashQuery other (.ordinary input)

theorem resolvedPreservesPublishedValues_probeFirstMissingInputCoordinate
    (input : HashInput) : ∀ slot coordinates,
    ResolvedPreservesPublished
      (probeFirstMissingInputCoordinate input slot coordinates)
  | _, [] => ResolvedPreservesPublished.pure ()
  | slot, coordinate :: remaining => by
      rw [probeFirstMissingInputCoordinate]
      exact (ResolvedPreservesPublished.of_preservesCoordinate fun other =>
        resolvedPreservesCoordinate_peekCoordinate other coordinate).bind fun value =>
          match value with
          | none => ResolvedPreservesPublished.of_preservesCoordinate fun other =>
              resolvedPreservesCoordinate_probe other
                ⟨coordinate, slotDigest slot input⟩
          | some _ => resolvedPreservesPublishedValues_probeFirstMissingInputCoordinate input
              (slot + 1) remaining

theorem resolvedPreservesPublishedValues_prepareLeafInputProbe
    (input : HashInput) (candidate : Probe)
    (lay : Layer) (tree : TreeIndex) (leafIdx : LeafIndex) :
    ResolvedPreservesPublished
      (prepareLeafInputProbe input candidate lay tree leafIdx) := by
  unfold prepareLeafInputProbe
  apply (ResolvedPreservesPublished.of_preservesCoordinate fun other =>
    resolvedPreservesCoordinate_peekCoordinate other candidate.coordinate).bind
  intro value
  cases value with
  | none =>
      exact ResolvedPreservesPublished.of_preservesCoordinate fun other =>
        resolvedPreservesCoordinate_probe other candidate
  | some output =>
      exact resolvedPreservesPublishedValues_probeFirstMissingInputCoordinate input 0
        ((Position.leaf lay tree leafIdx).children.map Coordinate.position)

theorem resolvedPreservesPublishedValues_probingHashQuery
    (parameter : PublicParameter) (input : HashInput) :
    ResolvedPreservesPublished (probingHashQuery parameter input) := by
  unfold probingHashQuery
  cases hprobe : decodeProbe? parameter input with
  | some candidate =>
      cases decodePosition? parameter input with
      | some position =>
          cases position with
          | leaf lay tree leafIdx =>
              exact (resolvedPreservesPublishedValues_prepareLeafInputProbe input candidate lay
                tree leafIdx).bind fun _ =>
                  resolvedPreservesPublishedValues_resolveKnownInput parameter
                    candidate.outputCoordinate input
          | chain | node | ftsLeaf | ftsNode | ftsRoots =>
              exact (ResolvedPreservesPublished.of_preservesCoordinate fun other =>
                resolvedPreservesCoordinate_probe other candidate).bind fun _ =>
                  resolvedPreservesPublishedValues_resolveKnownInput parameter
                    candidate.outputCoordinate input
      | none =>
          exact (ResolvedPreservesPublished.of_preservesCoordinate fun other =>
            resolvedPreservesCoordinate_probe other candidate).bind fun _ =>
              resolvedPreservesPublishedValues_resolveKnownInput parameter
                candidate.outputCoordinate input
  | none =>
      cases hposition : decodePosition? parameter input with
      | none =>
          exact ResolvedPreservesPublished.of_preservesCoordinate fun other =>
            resolvedPreservesCoordinate_splitHashQuery other (.ordinary input)
      | some position =>
          cases position with
          | chain | leaf =>
              exact resolvedPreservesPublishedValues_resolveKnownInput parameter _ input
          | node lay tree level nodeIdx =>
              exact (resolvedPreservesPublishedValues_probeFirstMissingInputCoordinate input 0
                ((Position.node lay tree level nodeIdx).children.map
                  Coordinate.position)).bind fun _ =>
                    resolvedPreservesPublishedValues_resolveKnownInput parameter _ input
          | ftsLeaf | ftsNode | ftsRoots =>
              exact ResolvedPreservesPublished.of_preservesCoordinate fun other =>
                resolvedPreservesCoordinate_splitHashQuery other (.ordinary input)

theorem resolvedPreservesPublishedValues_splitUniformImpl (n : Nat) :
    ResolvedPreservesPublished (splitUniformImpl n) := by
  intro context cache fuel table result hpublished hresult
  change some result ∈ support (runResolvedFromTable context fuel table
    (LazyRevealProbe.uniformQuery n >>= fun output => pure (output, cache))) at hresult
  rw [LazyRevealProbe.uniformQuery, runResolvedFromTable_uniform_query_bind,
    mem_support_bind_iff] at hresult
  obtain ⟨output, _houtput, hdone⟩ := hresult
  simp [runResolvedFromTable] at hdone
  subst result
  exact hpublished

def ResolvedPreservesPublishedImpl {spec : OracleSpec ι}
    (impl : QueryImpl spec
      (StateT SplitHashCache (OracleComp (LazyRevealProbe.World Coordinate)))) : Prop :=
  ∀ query, ResolvedPreservesPublished (impl query)

theorem ResolvedPreservesPublishedImpl.simulateQ
    {spec : OracleSpec ι}
    {impl : QueryImpl spec
      (StateT SplitHashCache (OracleComp (LazyRevealProbe.World Coordinate)))}
    (himpl : ResolvedPreservesPublishedImpl impl)
    (computation : OracleComp spec α) :
    ResolvedPreservesPublished (simulateQ impl computation) := by
  induction computation using OracleComp.inductionOn with
  | pure value => exact ResolvedPreservesPublished.pure value
  | query_bind query next ih =>
      rw [simulateQ_query_bind]
      exact (himpl query).bind ih

theorem resolvedPreservesPublishedValues_ensureCoordinate
    (coordinate : Coordinate) :
    ResolvedPreservesPublished (ensureCoordinate coordinate) :=
  ResolvedPreservesPublished.of_preservesCoordinate fun other =>
    resolvedPreservesCoordinate_ensure other coordinate

theorem resolvedPreservesPublishedValuesImpl_ordinaryHashImpl :
    ResolvedPreservesPublishedImpl ordinaryHashImpl :=
  fun input => ResolvedPreservesPublished.of_preservesCoordinate fun coordinate =>
    resolvedPreservesCoordinate_splitHashQuery coordinate (.ordinary input)

theorem resolvedPreservesPublishedValues_simulateQ_ordinaryHashImpl
    (computation : OracleComp HashSpec α) :
    ResolvedPreservesPublished (simulateQ ordinaryHashImpl computation) :=
  resolvedPreservesPublishedValuesImpl_ordinaryHashImpl.simulateQ computation

theorem resolvedPreservesPublishedValues_revealCoordinate (coordinate : Coordinate) :
    ResolvedPreservesPublished (revealCoordinate coordinate) := by
  unfold revealCoordinate
  exact (resolvedPreservesPublishedValues_revealCoordinateOutput coordinate).bind fun _ =>
    ResolvedPreservesPublished.pure _

theorem resolvedPreservesPublishedValues_revealPublishedCoordinate
    (coordinate : Coordinate) :
    ResolvedPreservesPublished (revealPublishedCoordinate coordinate) := by
  have hpreserves :=
    (resolvedPreservesPublishedValues_revealCoordinateOutput_publish coordinate).bind
      fun output => ResolvedPreservesPublished.pure (truncateHash output)
  simpa only [revealPublishedCoordinate, revealCoordinate, bind_assoc, pure_bind] using hpreserves

theorem resolvedPreservesPublishedValuesImpl_probingRomImpl
    (parameter : PublicParameter) :
    ResolvedPreservesPublishedImpl (probingRomImpl parameter) := by
  intro query
  cases query with
  | inl n => exact resolvedPreservesPublishedValues_splitUniformImpl n
  | inr input => exact resolvedPreservesPublishedValues_probingHashQuery parameter input

theorem resolvedPreservesPublishedValues_ensureFullChain
    (lay : Layer) (tree : TreeIndex) (leafIdx : LeafIndex) (chainIdx : ChainIndex) :
    ResolvedPreservesPublished (ensureFullChain lay tree leafIdx chainIdx) := by
  unfold ensureFullChain
  exact (resolvedPreservesPublished_sequenceFin _ fun step =>
    resolvedPreservesPublishedValues_ensureCoordinate
      (.position (.chain lay tree leafIdx chainIdx step))).bind fun _ =>
        ResolvedPreservesPublished.pure ()

theorem resolvedPreservesPublishedValues_ensureChainPrefix
    (lay : Layer) (tree : TreeIndex) (leafIdx : LeafIndex) (chainIdx : ChainIndex)
    (digit : Digit) :
    ResolvedPreservesPublished (ensureChainPrefix lay tree leafIdx chainIdx digit) := by
  unfold ensureChainPrefix
  exact (resolvedPreservesPublished_sequenceFin _ fun step => by
    split
    · exact resolvedPreservesPublishedValues_ensureCoordinate
        (.position (.chain lay tree leafIdx chainIdx step))
    · exact ResolvedPreservesPublished.pure ()).bind fun _ =>
        ResolvedPreservesPublished.pure ()

theorem resolvedPreservesPublishedValues_ensureOtsLeaf
    (lay : Layer) (tree : TreeIndex) (leafIdx : LeafIndex) :
    ResolvedPreservesPublished (ensureOtsLeaf lay tree leafIdx) := by
  unfold ensureOtsLeaf
  exact (resolvedPreservesPublished_sequenceFin _ fun chainIdx =>
    resolvedPreservesPublishedValues_ensureFullChain lay tree leafIdx chainIdx).bind fun _ =>
      resolvedPreservesPublishedValues_ensureCoordinate (.position (.leaf lay tree leafIdx))

theorem resolvedPreservesPublishedValues_ensureTreeNode
    (lay : Layer) (tree : TreeIndex) : ∀ level nodeIdx,
    ResolvedPreservesPublished (ensureTreeNode lay tree level nodeIdx)
  | 0, nodeIdx => by
      rw [ensureTreeNode]
      exact resolvedPreservesPublishedValues_ensureOtsLeaf lay tree (leafOfNat nodeIdx)
  | level + 1, nodeIdx => by
      rw [ensureTreeNode]
      exact (resolvedPreservesPublishedValues_ensureTreeNode lay tree level
        (2 * nodeIdx)).bind fun _ =>
          (resolvedPreservesPublishedValues_ensureTreeNode lay tree level
            (2 * nodeIdx + 1)).bind fun _ => by
              split
              · exact resolvedPreservesPublishedValues_ensureCoordinate _
              · exact ResolvedPreservesPublished.pure ()

theorem resolvedPreservesPublishedValues_maskedTreeNode
    (lay : Layer) (tree : TreeIndex) (level nodeIdx : Nat) :
    ResolvedPreservesPublished (maskedTreeNode lay tree level nodeIdx) := by
  cases level with
  | zero =>
      rw [maskedTreeNode]
      exact (resolvedPreservesPublishedValues_ensureTreeNode lay tree 0 nodeIdx).bind fun _ =>
        resolvedPreservesPublishedValues_revealCoordinate _
  | succ current =>
      rw [maskedTreeNode]
      exact (resolvedPreservesPublishedValues_ensureTreeNode lay tree (current + 1)
        nodeIdx).bind fun _ => by
          by_cases hlevel : current < maxLayerHeight
          · rw [dif_pos hlevel]
            exact resolvedPreservesPublishedValues_revealCoordinate _
          · rw [dif_neg hlevel]
            exact ResolvedPreservesPublished.pure 0

theorem resolvedPreservesPublishedValues_maskedTreeRoot
    (lay : Layer) (tree : TreeIndex) :
    ResolvedPreservesPublished (maskedTreeRoot lay tree) :=
  resolvedPreservesPublishedValues_maskedTreeNode lay tree (layerHeight lay) 0

theorem resolvedPreservesPublishedValues_ensureTreePath
    (lay : Layer) (tree : TreeIndex) (leafIdx : LeafIndex) :
    ResolvedPreservesPublished (ensureTreePath lay tree leafIdx) := by
  unfold ensureTreePath
  exact (resolvedPreservesPublished_sequenceFin _ fun level => by
    split
    · exact resolvedPreservesPublishedValues_ensureTreeNode lay tree level.val
        (Nat.xor (leafIdx.val / 2 ^ level.val) 1)
    · exact ResolvedPreservesPublished.pure ()).bind fun _ =>
        ResolvedPreservesPublished.pure ()

theorem resolvedPreservesPublishedValues_maskedLayerMessage
    (parameter : PublicParameter) (ftsSecret : Index → FtsTree → FtsLeaf → Digest)
    (index : Index) (lay : Layer) :
    ResolvedPreservesPublished (maskedLayerMessage parameter ftsSecret index lay) := by
  unfold maskedLayerMessage
  split
  · exact resolvedPreservesPublishedValues_maskedTreeRoot _ _
  · exact resolvedPreservesPublishedValues_simulateQ_ordinaryHashImpl _

theorem resolvedPreservesPublishedValues_maskedOtsSignFrom
    (parameter : PublicParameter) (lay : Layer) (tree : TreeIndex)
    (leafIdx : LeafIndex) (message : Digest) : ∀ attempts counter,
    ResolvedPreservesPublished
      (maskedOtsSignFrom parameter lay tree leafIdx message attempts counter)
  | 0, _ => ResolvedPreservesPublished.pure none
  | attempts + 1, counter => by
      rw [maskedOtsSignFrom]
      exact (resolvedPreservesPublishedValues_simulateQ_ordinaryHashImpl _).bind fun encoded =>
        match encoded with
        | none => resolvedPreservesPublishedValues_maskedOtsSignFrom parameter lay tree leafIdx
            message attempts (counter + 1)
        | some encoding =>
            (resolvedPreservesPublished_sequenceFin _ fun chainIdx =>
              resolvedPreservesPublishedValues_ensureChainPrefix lay tree leafIdx chainIdx
                (encoding chainIdx)).bind fun _ => ResolvedPreservesPublished.pure _

theorem resolvedPreservesPublishedValues_maskedOtsSign
    (parameter : PublicParameter) (lay : Layer) (tree : TreeIndex)
    (leafIdx : LeafIndex) (message : Digest) :
    ResolvedPreservesPublished
      (maskedOtsSign parameter lay tree leafIdx message) :=
  resolvedPreservesPublishedValues_maskedOtsSignFrom parameter lay tree leafIdx message
    encodingAttemptLimit 0

theorem resolvedPreservesPublishedValues_maskedSignLayer
    (parameter : PublicParameter) (ftsSecret : Index → FtsTree → FtsLeaf → Digest)
    (index : Index) (lay : Layer) :
    ResolvedPreservesPublished (maskedSignLayer parameter ftsSecret index lay) := by
  unfold maskedSignLayer
  exact (resolvedPreservesPublishedValues_maskedLayerMessage parameter ftsSecret index lay).bind
    fun message =>
      (resolvedPreservesPublishedValues_maskedOtsSign parameter lay (treeIndexAt index lay)
        (leafIndexAt index lay) message).bind fun result =>
          match result with
          | none => ResolvedPreservesPublished.pure none
          | some _ =>
              (resolvedPreservesPublishedValues_ensureTreePath lay (treeIndexAt index lay)
                (leafIndexAt index lay)).bind fun _ => ResolvedPreservesPublished.pure _

theorem resolvedPreservesPublishedValues_revealLayerValues
    (index : Index) (lay : Layer) (encoding : ChainIndex → Digit) :
    ResolvedPreservesPublished (revealLayerValues index lay encoding) := by
  unfold revealLayerValues
  exact (resolvedPreservesPublished_sequenceFin _ fun chainIdx =>
    resolvedPreservesPublishedValues_revealPublishedCoordinate
      (chainValueCoordinate lay (treeIndexAt index lay) (leafIndexAt index lay) chainIdx
        (encoding chainIdx))).bind fun _ =>
          (resolvedPreservesPublished_sequenceFin _ fun level => by
            split
            · cases hlevelValue : level.val with
              | zero => exact resolvedPreservesPublishedValues_revealPublishedCoordinate _
              | succ current =>
                  rw [show current + 1 = Nat.succ current by omega]
                  change ResolvedPreservesPublished
                    (if hlevel : current < maxLayerHeight then
                      revealPublishedCoordinate (.position (.node lay (treeIndexAt index lay)
                        ⟨current, hlevel⟩ (leafOfNat
                          (Nat.xor ((leafIndexAt index lay).val / 2 ^ (current + 1)) 1))))
                    else pure 0)
                  by_cases hlevel : current < maxLayerHeight
                  · rw [dif_pos hlevel]
                    exact resolvedPreservesPublishedValues_revealPublishedCoordinate _
                  · rw [dif_neg hlevel]
                    exact ResolvedPreservesPublished.pure 0
            · exact ResolvedPreservesPublished.pure 0).bind fun _ =>
                  ResolvedPreservesPublished.pure _

theorem resolvedPreservesPublishedValues_ordinarySignDigestLoop
    (secretKey : SecretKey) (attempts : Nat) (message : Message) :
    ResolvedPreservesPublished
      (simulateQ ordinaryRomImpl (signDigestLoop attempts secretKey message)) := by
  induction attempts with
  | zero =>
      rw [signDigestLoop, simulateQ_pure]
      exact ResolvedPreservesPublished.pure none
  | succ attempts ih =>
      rw [signDigestLoop, simulateQ_bind]
      have hrandomness : ResolvedPreservesPublished
          (simulateQ ordinaryRomImpl (liftM sampleRandomness)) := by
        rw [ordinaryRomImpl, QueryImpl.simulateQ_add_liftM_left]
        exact (show ResolvedPreservesPublishedImpl splitUniformImpl from
          fun n => resolvedPreservesPublishedValues_splitUniformImpl n).simulateQ
            sampleRandomness
      exact hrandomness.bind fun randomness => by
        rw [simulateQ_bind]
        have hattempt : ResolvedPreservesPublished
            (simulateQ ordinaryRomImpl
              (liftM (signAttempt secretKey message randomness :
                OracleComp HashSpec (Option (Index × (DigestTree → FtsLeaf)))))) := by
          rw [ordinaryRomImpl, QueryImpl.simulateQ_add_liftM_right]
          exact resolvedPreservesPublishedValues_simulateQ_ordinaryHashImpl _
        exact hattempt.bind fun attempt => by
          cases attempt with
          | none => exact ih
          | some selected => exact ResolvedPreservesPublished.pure _

theorem resolvedPreservesPublishedValues_maskedSignAfterDigest
    (parameter : PublicParameter) (ftsSecret : Index → FtsTree → FtsLeaf → Digest)
    (randomness : Randomness) (index : Index) (leaves : DigestTree → FtsLeaf) :
    ResolvedPreservesPublished
      (maskedSignAfterDigest parameter ftsSecret randomness index leaves) := by
  unfold maskedSignAfterDigest
  exact (resolvedPreservesPublishedValues_simulateQ_ordinaryHashImpl _).bind fun _ =>
    (resolvedPreservesPublished_sequenceFin _ fun lay =>
      resolvedPreservesPublishedValues_maskedSignLayer parameter ftsSecret index lay).bind
        fun layers => match traverseOption layers with
        | none => ResolvedPreservesPublished.pure none
        | some parts => (resolvedPreservesPublished_sequenceFin _ fun lay =>
            resolvedPreservesPublishedValues_revealLayerValues index lay (parts lay).2).bind
              fun _ => ResolvedPreservesPublished.pure _

theorem resolvedPreservesPublishedValues_maskedSign
    (parameter : PublicParameter) (root : Digest)
    (ftsSecret : Index → FtsTree → FtsLeaf → Digest) (message : Message) :
    ResolvedPreservesPublished (maskedSign parameter root ftsSecret message) := by
  unfold maskedSign
  exact (resolvedPreservesPublishedValues_ordinarySignDigestLoop
    (⟨parameter, root, fun _ _ _ _ => 0, ftsSecret⟩ : SecretKey) digestAttemptLimit
      message).bind fun selected => match selected with
        | none => ResolvedPreservesPublished.pure none
        | some data => resolvedPreservesPublishedValues_maskedSignAfterDigest parameter ftsSecret
            data.1 data.2.1 data.2.2

theorem PublishedValues.of_privateStateAgrees
    {left right : DeferredContext} (hpublished : PublishedValues right.state)
    (hagrees : PrivateStateAgrees left right) : PublishedValues left.state := by
  intro coordinate hrevealed
  rw [hagrees.1]
  exact hpublished coordinate (by simpa [hagrees.2.1] using hrevealed)

theorem resolvedPreservesPublishedValues_publishChronologicalSignature
    (ftsSecret : Index → FtsTree → FtsLeaf → Digest)
    (randomness : Randomness) (index : Index) (leaves : DigestTree → FtsLeaf)
    (ftsPath : FtsTree → Fin ftsTreeHeight → Digest)
    (layers : Layer → Option ChronologicalLayerPart) :
    ResolvedPreservesPublished
      (publishChronologicalSignature ftsSecret randomness index leaves ftsPath layers) := by
  unfold publishChronologicalSignature
  cases hparts : traverseOption layers with
  | none => exact ResolvedPreservesPublished.pure none
  | some parts =>
      exact (resolvedPreservesPublished_sequenceFin _ fun lay =>
        resolvedPreservesPublishedValues_revealLayerValues index lay
          (parts lay).encoding).bind fun _ => ResolvedPreservesPublished.pure _

theorem publishedValues_of_mem_selectDeferredLayer
    (parameter : PublicParameter) (table : OtsSecretIndex → HashOutput)
    (ftsSecret : Index → FtsTree → FtsLeaf → Digest) (index : Index)
    (lay : Layer) (input result : ResolvedRunResult DeferredLayerStore)
    (hpublished : PublishedValues input.context.state)
    (hresult : some result ∈ support
      (selectDeferredLayer parameter table ftsSecret index lay input)) :
    PublishedValues result.context.state := by
  unfold selectDeferredLayer at hresult
  rw [mem_support_bind_iff] at hresult
  obtain ⟨selectedOption, hselected, hreturn⟩ := hresult
  cases selectedOption with
  | none => simp at hreturn
  | some selected =>
      simp only [support_pure, Set.mem_singleton_iff] at hreturn
      have hresultEq := Option.some.inj hreturn
      subst result
      exact resolvedPreservesPublishedValues_maskedSignLayer parameter ftsSecret index lay
        input.context input.value.cache input.remaining table selected hpublished hselected

theorem publishedValues_of_mem_resolveDeferredLayer
    (table : OtsSecretIndex → HashOutput) (index : Index) (lay : Layer)
    (input result : ResolvedRunResult DeferredLayerStore)
    (hpublished : PublishedValues input.context.state)
    (hresult : some result ∈ support (resolveDeferredLayer table index lay input)) :
    PublishedValues result.context.state := by
  unfold resolveDeferredLayer at hresult
  cases hselection : input.value.selected lay with
  | none =>
      simp only [hselection, support_pure, Set.mem_singleton_iff] at hresult
      have hresultEq := Option.some.inj hresult
      subst result
      exact hpublished
  | some selection =>
      rcases selection with ⟨counter, encoding⟩
      simp only [hselection, mem_support_bind_iff] at hresult
      obtain ⟨resolvedOption, hresolved, hreturn⟩ := hresult
      cases resolvedOption with
      | none => simp at hreturn
      | some resolved =>
          rcases resolved with ⟨finalContext, values⟩
          simp only [support_pure, Set.mem_singleton_iff] at hreturn
          have hresultEq := Option.some.inj hreturn
          subst result
          exact hpublished.of_privateStateAgrees
            (privateStateAgrees_resolveDeferredLayerValues table index lay encoding input.context
              finalContext values hresolved)

theorem publishedValues_of_mem_runDeferredLayerOperation
    (parameter : PublicParameter) (table : OtsSecretIndex → HashOutput)
    (ftsSecret : Index → FtsTree → FtsLeaf → Digest) (index : Index)
    (operation : DeferredLayerOperation)
    (input result : ResolvedRunResult DeferredLayerStore)
    (hpublished : PublishedValues input.context.state)
    (hresult : some result ∈ support
      (runDeferredLayerOperation parameter table ftsSecret index operation (some input))) :
    PublishedValues result.context.state := by
  cases operation with
  | select lay =>
      exact publishedValues_of_mem_selectDeferredLayer parameter table ftsSecret index lay input
        result hpublished hresult
  | resolve lay =>
      exact publishedValues_of_mem_resolveDeferredLayer table index lay input result hpublished
        hresult

theorem publishedValues_of_mem_runDeferredLayerSchedule
    (parameter : PublicParameter) (table : OtsSecretIndex → HashOutput)
    (ftsSecret : Index → FtsTree → FtsLeaf → Digest) (index : Index) :
    ∀ operations (input result : ResolvedRunResult DeferredLayerStore),
      PublishedValues input.context.state →
      some result ∈ support
        (runDeferredLayerSchedule parameter table ftsSecret index operations (some input)) →
      PublishedValues result.context.state
  | [], input, result, hpublished, hresult => by
      simp [runDeferredLayerSchedule] at hresult
      subst result
      exact hpublished
  | operation :: remaining, input, result, hpublished, hresult => by
      rw [runDeferredLayerSchedule, mem_support_bind_iff] at hresult
      obtain ⟨stepOption, hstep, hrest⟩ := hresult
      cases stepOption with
      | none => simp at hrest
      | some step =>
          exact publishedValues_of_mem_runDeferredLayerSchedule parameter table ftsSecret index
            remaining step result
              (publishedValues_of_mem_runDeferredLayerOperation parameter table ftsSecret index
                operation input step hpublished hstep)
              hrest

theorem publishedValues_of_mem_publishDeferredChronologicalSignature
    (ftsSecret : Index → FtsTree → FtsLeaf → Digest)
    (randomness : Randomness) (index : Index) (leaves : DigestTree → FtsLeaf)
    (ftsPath : FtsTree → Fin ftsTreeHeight → Digest)
    (input : ResolvedRunResult DeferredLayerStore)
    (result : ResolvedRunResult (Option Signature × SplitHashCache))
    (hpublished : PublishedValues input.context.state)
    (hresult : some result ∈ support
      (publishDeferredChronologicalSignature ftsSecret randomness index leaves ftsPath
        (some input))) :
    PublishedValues result.context.state := by
  unfold publishDeferredChronologicalSignature at hresult
  exact resolvedPreservesPublishedValues_publishChronologicalSignature ftsSecret randomness index
    leaves ftsPath (chronologicalPartsOfStore input.value) input.context input.value.cache
      input.remaining input.table result hpublished hresult

theorem publishedValues_of_mem_runDeferredChronologicalLayersAndPublish
    (parameter : PublicParameter) (table : OtsSecretIndex → HashOutput)
    (ftsSecret : Index → FtsTree → FtsLeaf → Digest)
    (randomness : Randomness) (index : Index) (leaves : DigestTree → FtsLeaf)
    (ftsPath : FtsTree → Fin ftsTreeHeight → Digest)
    (context : DeferredContext) (fuel : Nat) (cache : SplitHashCache)
    (result : ResolvedRunResult (Option Signature × SplitHashCache))
    (hpublished : PublishedValues context.state)
    (hresult : some result ∈ support
      (runDeferredChronologicalLayersAndPublish parameter table ftsSecret randomness index leaves
        ftsPath context fuel cache)) :
    PublishedValues result.context.state := by
  unfold runDeferredChronologicalLayersAndPublish at hresult
  rw [mem_support_bind_iff] at hresult
  obtain ⟨layersOption, hlayers, hpublish⟩ := hresult
  cases layersOption with
  | none => simp [publishDeferredChronologicalSignature] at hpublish
  | some layers =>
      have hlayersPublished := publishedValues_of_mem_runDeferredLayerSchedule parameter table
        ftsSecret index chronologicalLayerSchedule
          { context := context, remaining := fuel, value := emptyDeferredLayerStore cache,
            table := table }
          layers hpublished hlayers
      exact publishedValues_of_mem_publishDeferredChronologicalSignature ftsSecret randomness
        index leaves ftsPath layers result hlayersPublished hpublish

theorem publishedValues_of_mem_runDeferredChronologicalSignAfterDigest
    (parameter : PublicParameter) (table : OtsSecretIndex → HashOutput)
    (ftsSecret : Index → FtsTree → FtsLeaf → Digest)
    (randomness : Randomness) (index : Index) (leaves : DigestTree → FtsLeaf)
    (context : DeferredContext) (fuel : Nat) (cache : SplitHashCache)
    (result : ResolvedRunResult (Option Signature × SplitHashCache))
    (hpublished : PublishedValues context.state)
    (hresult : some result ∈ support
      (runDeferredChronologicalSignAfterDigest parameter table ftsSecret randomness index leaves
        context fuel cache)) :
    PublishedValues result.context.state := by
  unfold runDeferredChronologicalSignAfterDigest at hresult
  rw [mem_support_bind_iff] at hresult
  obtain ⟨ftsOption, hfts, hrest⟩ := hresult
  cases ftsOption with
  | none => simp at hrest
  | some ftsResult =>
      have hftsPublished := resolvedPreservesPublishedValues_simulateQ_ordinaryHashImpl
        (ftsOpen parameter index leaves (ftsSecret index)) context cache fuel table ftsResult
          hpublished hfts
      exact publishedValues_of_mem_runDeferredChronologicalLayersAndPublish parameter table
        ftsSecret randomness index leaves ftsResult.value.1 ftsResult.context
          ftsResult.remaining ftsResult.value.2 result hftsPublished hrest

theorem publishedValues_of_mem_runDeferredChronologicalSign
    (parameter : PublicParameter) (root : Digest)
    (table : OtsSecretIndex → HashOutput)
    (ftsSecret : Index → FtsTree → FtsLeaf → Digest) (message : Message)
    (context : DeferredContext) (fuel : Nat) (cache : SplitHashCache)
    (result : ResolvedRunResult (Option Signature × SplitHashCache))
    (hpublished : PublishedValues context.state)
    (hresult : some result ∈ support
      (runDeferredChronologicalSign parameter root table ftsSecret message context fuel cache)) :
    PublishedValues result.context.state := by
  unfold runDeferredChronologicalSign at hresult
  rw [mem_support_bind_iff] at hresult
  obtain ⟨selectedOption, hselected, hrest⟩ := hresult
  cases selectedOption with
  | none => simp at hrest
  | some selected =>
      have hselectedPublished := resolvedPreservesPublishedValues_ordinarySignDigestLoop
        (⟨parameter, root, fun _ _ _ _ => 0, ftsSecret⟩ : SecretKey) digestAttemptLimit message
          context cache fuel table selected hpublished hselected
      cases hvalue : selected.value.1 with
      | none =>
          simp only [hvalue, support_pure, Set.mem_singleton_iff] at hrest
          have hresultEq := Option.some.inj hrest
          subst result
          exact hselectedPublished
      | some digestResult =>
          rcases digestResult with ⟨randomness, selectedIndex, leaves⟩
          simp only [hvalue] at hrest
          exact publishedValues_of_mem_runDeferredChronologicalSignAfterDigest parameter table
            ftsSecret randomness selectedIndex leaves selected.context selected.remaining
              selected.value.2 result hselectedPublished hrest

theorem valid_of_mem_runDeferredChronologicalSign
    (parameter : PublicParameter) (root : Digest)
    (table : OtsSecretIndex → HashOutput)
    (ftsSecret : Index → FtsTree → FtsLeaf → Digest) (message : Message)
    (context : DeferredContext) (fuel : Nat) (cache : SplitHashCache)
    (result : ResolvedRunResult (Option Signature × SplitHashCache))
    (hvalid : context.Valid) (hcompletable : DeferredCompletable table context)
    (hresult : some result ∈ support
      (runDeferredChronologicalSign parameter root table ftsSecret message context fuel cache)) :
    result.context.Valid := by
  have hstarts := startTableAgrees_of_deferredCompletable hcompletable
  have hview := finalizationViewEq_of_deferredCompletion_iff hvalid hvalid hstarts hstarts rfl
    hcompletable (fun _ => Iff.rfl)
  have hrelation :=
    relTriple_runResolvedFromTable_maskedPublishedChronologicalSign_finalization parameter root
      table ftsSecret message context context fuel cache cache
        ⟨hview, hvalid, hvalid, hcompletable⟩ rfl rfl
  obtain ⟨leftOption, _hleft, hrelated⟩ :=
    exists_right_of_relTriple_of_mem_support
      (OracleComp.ProgramLogic.Relational.relTriple_symm hrelation) hresult
  cases leftOption with
  | none => simp [FinalizationMaterializedRunEq] at hrelated
  | some leftResult =>
      exact hrelated.2.1.2.2.1

theorem evalDist_finishObserve_canonicalContinuation_canonicalizeResolvedRun
    (table : OtsSecretIndex → HashOutput)
    (next : α → StateT SplitHashCache
      (OracleComp (LazyRevealProbe.World Coordinate)) β)
    (result : Option (ResolvedRunResult (α × SplitHashCache)))
    (hconsistent : ∀ resolved, result = some resolved →
      resolved.context.ValuesConsistent)
    (hpublished : ∀ resolved, result = some resolved →
      PublishedValues resolved.context.state) :
    evalDist (finishObserve (canonicalContinuationObserve table next)
        (canonicalizeResolvedRun table result)) =
      evalDist (finishObserve (canonicalContinuationObserve table next) result) := by
  cases result with
  | none => rfl
  | some result =>
      have hresultConsistent := hconsistent result rfl
      have hresultPublished := hpublished result rfl
      have hcanonicalPublished :=
        hresultPublished.to_canonicalizedMaterializedValues (table := table)
      simp only [canonicalizeResolvedRun, finishObserve]
      unfold canonicalContinuationObserve
      simp only [hresultPublished, hcanonicalPublished, ↓reduceIte]
      rw [canonicalizeMaterializedValues_idempotent table result.context
        hresultConsistent]

theorem evalDist_runResolvedFromTable_canonicalize_then_canonicalContinuation
    (table : OtsSecretIndex → HashOutput)
    (computation : StateT SplitHashCache
      (OracleComp (LazyRevealProbe.World Coordinate)) α)
    (next : α → StateT SplitHashCache
      (OracleComp (LazyRevealProbe.World Coordinate)) β)
    (context : DeferredContext) (fuel : Nat) (cache : SplitHashCache)
    (hconsistent : context.ValuesConsistent)
    (hstarts : StartTableAgrees context.state table)
    (hpublished : PublishedValues context.state)
    (hpreserves : ResolvedPreservesPublished computation) :
    evalDist (runResolvedFromTable context fuel table (computation.run cache) >>= fun result =>
        finishObserve (canonicalContinuationObserve table next)
          (canonicalizeResolvedRun table result)) =
      evalDist (runResolvedObserve (canonicalContinuationObserve table next) context fuel table
        (computation.run cache)) := by
  unfold runResolvedObserve
  apply evalDist_bind_congr
  intro result hresult
  cases result with
  | none => rfl
  | some result =>
      have hcore := resolvedCore_of_mem_runResolvedFromTable (computation.run cache) context fuel
        table result hconsistent hstarts hresult
      have hresultPublished := hpreserves context cache fuel table result hpublished hresult
      exact evalDist_finishObserve_canonicalContinuation_canonicalizeResolvedRun table next
        (some result) (by simp [hcore.2.1]) (by simp [hresultPublished])

theorem evalDist_canonicalDeferredAdversaryImpl_hash_canonicalContinuation
    (parameter : PublicParameter) (root : Digest)
    (table : OtsSecretIndex → HashOutput)
    (ftsSecret : Index → FtsTree → FtsLeaf → Digest)
    (query : OracleWorld.Domain)
    (next : OracleWorld.Range query → StateT SplitHashCache
      (OracleComp (LazyRevealProbe.World Coordinate)) α)
    (context : DeferredContext) (fuel : Nat) (cache : SplitHashCache)
    (hconsistent : context.ValuesConsistent)
    (hstarts : StartTableAgrees context.state table)
    (hpublished : PublishedValues context.state) :
    evalDist
        (canonicalDeferredAdversaryImpl parameter root table ftsSecret (.inl query) context fuel
          table cache >>= finishObserve (canonicalContinuationObserve table next)) =
      evalDist (runResolvedObserve (canonicalContinuationObserve table next) context fuel table
        ((probingRomImpl parameter query).run cache)) := by
  rw [canonicalDeferredAdversaryImpl]
  simp only [bind_assoc, pure_bind]
  exact evalDist_runResolvedFromTable_canonicalize_then_canonicalContinuation table
    (probingRomImpl parameter query) next context fuel cache hconsistent hstarts hpublished
      (resolvedPreservesPublishedValuesImpl_probingRomImpl parameter query)

theorem evalDist_canonicalDeferredAdversaryImpl_sign_canonicalContinuation
    (parameter : PublicParameter) (root : Digest)
    (table : OtsSecretIndex → HashOutput)
    (ftsSecret : Index → FtsTree → FtsLeaf → Digest) (message : Message)
    (next : Option Signature → StateT SplitHashCache
      (OracleComp (LazyRevealProbe.World Coordinate)) α)
    (context : DeferredContext) (fuel : Nat) (cache : SplitHashCache)
    (hvalid : context.Valid) (hcompletable : DeferredCompletable table context)
    (hpublished : PublishedValues context.state) :
    evalDist
        (canonicalDeferredAdversaryImpl parameter root table ftsSecret (.inr message) context fuel
          table cache >>= finishObserve (canonicalContinuationObserve table next)) =
      evalDist (runResolvedObserve (canonicalContinuationObserve table next) context fuel table
        ((maskedSign parameter root ftsSecret message).run cache)) := by
  rw [canonicalDeferredAdversaryImpl]
  simp only [bind_assoc, pure_bind]
  calc
    _ = evalDist (runDeferredChronologicalSign parameter root table ftsSecret message context fuel
          cache >>= finishObserve (canonicalContinuationObserve table next)) := by
      apply evalDist_bind_congr
      intro result hresult
      cases result with
      | none => rfl
      | some result =>
          have hresultValid := valid_of_mem_runDeferredChronologicalSign parameter root table
            ftsSecret message context fuel cache result hvalid hcompletable hresult
          have hresultPublished := publishedValues_of_mem_runDeferredChronologicalSign parameter
            root table ftsSecret message context fuel cache result hpublished hresult
          exact evalDist_finishObserve_canonicalContinuation_canonicalizeResolvedRun table next
            (some result) (by simp [hresultValid.valuesConsistent])
              (by simp [hresultPublished])
    _ = _ := evalDist_runDeferredChronologicalSign_canonicalObserve_eq_maskedSign parameter root
      table ftsSecret message context fuel cache next hvalid hcompletable

end SphincsSecurity.Concrete.OtsProbeSimulation
