import SphincsSecurity.Proof.OtsProbeResolvedBoundaryPrivateWitnessOrdinalHiddenFreshSigner

/-! Verifier hash calls publish every materialized value, so inserting canonicalization between them preserves the execution distribution. -/

namespace SphincsSecurity.Concrete.OtsProbeSimulation

open OracleComp OracleSpec

theorem preservesCoordinateMaterializedPublished_revealPublishedCoordinate_any
    (coordinate other : Coordinate) :
    PreservesCoordinateMaterializedPublished coordinate (revealPublishedCoordinate other) := by
  by_cases heq : coordinate = other
  · subst other
    have h := (preservesCoordinateMaterializedPublished_revealOutput_publish coordinate).bind
      (fun output => (preservesCoordinate_pure coordinate (truncateHash output)).to_materializedPublished)
    simpa only [revealPublishedCoordinate, revealCoordinate, bind_assoc, pure_bind] using h
  · unfold revealPublishedCoordinate
    exact ((preservesCoordinate_revealCoordinate_of_ne coordinate other heq).bind fun value =>
      (preservesCoordinate_publishCoordinate_of_ne coordinate other heq).bind fun _ =>
        preservesCoordinate_pure coordinate value).to_materializedPublished

theorem preservesCoordinateMaterializedPublished_maskedPublishedTreeRoot
    (coordinate : Coordinate) :
    PreservesCoordinateMaterializedPublished coordinate maskedPublishedTreeRoot := by
  unfold maskedPublishedTreeRoot
  exact (preservesCoordinate_ensureTreeNode coordinate topLayer rootTree
    (layerHeight topLayer) 0).to_materializedPublished.bind fun _ =>
      preservesCoordinateMaterializedPublished_revealPublishedCoordinate_any coordinate _

theorem CanonicalMaterializedValues.canonicalize_eq
    (hcanonical : CanonicalMaterializedValues table context) :
    canonicalizeMaterializedValues table context = context := by
  unfold canonicalizeMaterializedValues
  rw [← hcanonical]

theorem CanonicalMaterializedValues.materializedPublished
    (hcanonical : CanonicalMaterializedValues table context) (coordinate : Coordinate) :
    CoordinateMaterializedPublished coordinate context.state := by
  intro hvalue
  by_contra hhidden
  exact hvalue (by rw [congrFun hcanonical coordinate]; simp [publicMaterializedValues, hhidden])

theorem canonicalMaterializedValues_of_published
    (table : OtsSecretIndex → HashOutput) (context : DeferredContext)
    (hstarts : StartTableAgrees context.state table)
    (hpublished : PublishedValues context.state)
    (hmaterialized : ∀ coordinate, CoordinateMaterializedPublished coordinate context.state) :
    CanonicalMaterializedValues table context := by
  funext coordinate
  unfold publicMaterializedValues
  by_cases hrevealed : coordinate ∈ context.state.revealed
  · simp only [hrevealed, ↓reduceIte]
    cases hvalue : context.state.values coordinate with
    | none => exact False.elim (hpublished coordinate hrevealed hvalue)
    | some output =>
        cases coordinate with
        | chainStart lay tree leafIdx chainIdx =>
            have htable := hstarts ⟨lay, tree, leafIdx, chainIdx⟩ output hvalue
            simpa [resolvedCompletionValue] using congrArg some htable
        | position position => simp [resolvedCompletionValue, DeferredContext.positionValue, hvalue]
  · simp only [hrevealed, ↓reduceIte]
    by_contra hvalue
    exact hrevealed (hmaterialized coordinate hvalue)

theorem preservesCoordinate_probeFirstMissingInputCoordinate
    (coordinate : Coordinate) (input : HashInput) : ∀ slot coordinates,
    PreservesCoordinate coordinate (probeFirstMissingInputCoordinate input slot coordinates)
  | _, [] => preservesCoordinate_pure coordinate ()
  | slot, other :: remaining => by
      rw [probeFirstMissingInputCoordinate]
      exact ((rawReadOnly_peekCoordinate other).preservesCoordinate coordinate).bind fun value =>
        match value with
        | none => preservesCoordinate_probe coordinate ⟨other, slotDigest slot input⟩
        | some _ => preservesCoordinate_probeFirstMissingInputCoordinate coordinate input
            (slot + 1) remaining

theorem preservesCoordinate_prepareLeafInputProbe
    (coordinate : Coordinate) (input : HashInput) (candidate : Probe)
    (lay : Layer) (tree : TreeIndex) (leafIdx : LeafIndex) :
    PreservesCoordinate coordinate (prepareLeafInputProbe input candidate lay tree leafIdx) := by
  unfold prepareLeafInputProbe
  exact ((rawReadOnly_peekCoordinate candidate.coordinate).preservesCoordinate coordinate).bind
    fun value => match value with
    | none => preservesCoordinate_probe coordinate candidate
    | some _ => preservesCoordinate_probeFirstMissingInputCoordinate coordinate input 0 _

theorem preservesCoordinateMaterializedPublished_resolveKnownInput_any
    (parameter : PublicParameter) (coordinate other : Coordinate) (input : HashInput) :
    PreservesCoordinateMaterializedPublished coordinate (resolveKnownInput parameter other input) := by
  by_cases heq : coordinate = other
  · subst other
    exact preservesCoordinateMaterializedPublished_resolveKnownInput parameter coordinate input
  · exact (preservesCoordinate_resolveKnownInput_of_ne parameter coordinate other input heq).to_materializedPublished

theorem preservesCoordinateMaterializedPublished_probingHashQuery
    (parameter : PublicParameter) (coordinate : Coordinate) (input : HashInput) :
    PreservesCoordinateMaterializedPublished coordinate (probingHashQuery parameter input) := by
  unfold probingHashQuery
  cases decodeProbe? parameter input with
  | some candidate =>
      cases decodePosition? parameter input with
      | some position =>
          cases position with
          | leaf lay tree leafIdx =>
              exact (preservesCoordinate_prepareLeafInputProbe coordinate input candidate lay tree
                leafIdx).to_materializedPublished.bind fun _ =>
                  preservesCoordinateMaterializedPublished_resolveKnownInput_any parameter coordinate _ input
          | chain | node | ftsLeaf | ftsNode | ftsRoots =>
              exact (preservesCoordinate_probe coordinate candidate).to_materializedPublished.bind
                fun _ => preservesCoordinateMaterializedPublished_resolveKnownInput_any parameter coordinate _ input
      | none =>
          exact (preservesCoordinate_probe coordinate candidate).to_materializedPublished.bind
            fun _ => preservesCoordinateMaterializedPublished_resolveKnownInput_any parameter coordinate _ input
  | none =>
      cases decodePosition? parameter input with
      | none => exact (preservesCoordinate_splitHashQuery coordinate (.ordinary input)).to_materializedPublished
      | some position =>
          cases position with
          | chain | leaf => exact preservesCoordinateMaterializedPublished_resolveKnownInput_any parameter coordinate _ input
          | node lay tree level nodeIdx =>
              exact (preservesCoordinate_probeFirstMissingInputCoordinate coordinate input 0
                ((Position.node lay tree level nodeIdx).children.map Coordinate.position)).to_materializedPublished.bind
                  fun _ => preservesCoordinateMaterializedPublished_resolveKnownInput_any parameter coordinate _ input
          | ftsLeaf | ftsNode | ftsRoots =>
              exact (preservesCoordinate_splitHashQuery coordinate (.ordinary input)).to_materializedPublished

theorem preservesCoordinateMaterializedPublished_probingRomImpl
    (parameter : PublicParameter) (coordinate : Coordinate) (query : OracleWorld.Domain) :
    PreservesCoordinateMaterializedPublished coordinate (probingRomImpl parameter query) := by
  cases query with
  | inl n =>
      change PreservesCoordinateMaterializedPublished coordinate (splitUniformImpl n)
      have h := preservesCoordinate_simulateQ_splitUniformImpl coordinate (liftM (unifSpec.query n) : ProbComp (Fin (n + 1)))
      simpa [splitUniformImpl] using h.to_materializedPublished
  | inr input => exact preservesCoordinateMaterializedPublished_probingHashQuery parameter coordinate input

theorem evalDist_directBoundaryObserve_eq_flat_of_public
    (impl : QueryImpl spec
      (StateT SplitHashCache (OracleComp (LazyRevealProbe.World Coordinate))))
    (hpub : PreservesPublishedValuesImpl impl)
    (hmat : ∀ query coordinate, PreservesCoordinateMaterializedPublished coordinate (impl query))
    (computation : OracleComp spec α)
    (observe : DeferredContext → Nat → (α × SplitHashCache) → ProbComp Bool)
    (context : DeferredContext) (fuel : Nat)
    (table : OtsSecretIndex → HashOutput) (cache : SplitHashCache)
    (hconsistent : context.ValuesConsistent)
    (hstarts : StartTableAgrees context.state table)
    (hpublished : PublishedValues context.state)
    (hcanonical : CanonicalMaterializedValues table context) :
    evalDist (directBoundaryObserve impl computation observe context fuel table cache) =
      evalDist (runDirectResolvedObserve observe context fuel table
        ((simulateQ impl computation).run cache)) := by
  induction computation using OracleComp.inductionOn generalizing context fuel cache with
  | pure value =>
      simp [directBoundaryObserve, runDirectResolvedObserve, runDirectResolvedFromTable]
  | query_bind query next ih =>
      rw [directBoundaryObserve, OracleComp.construct_query_bind, simulateQ_query_bind,
        StateT.run_bind]
      unfold runDirectResolvedObserve
      rw [runDirectResolvedFromTable_bind_general, bind_assoc]
      apply evalDist_bind_congr
      intro result hresult
      cases result with
      | none => simp
      | some result =>
          have hcore := resolvedCore_of_mem_runDirectResolvedFromTable
            ((impl query).run cache) context fuel table result hconsistent hstarts hresult
          have hraw := raw_done_of_mem_runDirectResolvedFromTable
            ((impl query).run cache) context fuel table result hresult
          have hnextPub := hpub query context.state cache fuel result.context.state
            result.remaining result.value.1 result.value.2 hpublished hraw
          have hnextMat : ∀ coordinate,
              CoordinateMaterializedPublished coordinate result.context.state := by
            intro coordinate
            exact hmat query coordinate context.state cache fuel result.context.state
              result.remaining result.value.1 result.value.2
              (hcanonical.materializedPublished coordinate) hraw
          have hnextCanonical := canonicalMaterializedValues_of_published table result.context
            hcore.2.2 hnextPub hnextMat
          simp only [finishObserve, canonicalizeObserve, hnextPub, ↓reduceIte,
            hnextCanonical.canonicalize_eq, hcore.1]
          exact ih result.value.1 result.context result.remaining result.value.2
            hcore.2.1 hcore.2.2 hnextPub hnextCanonical

theorem evalDist_directBoundaryObserve_eq_of_canonical
    (impl : QueryImpl spec
      (StateT SplitHashCache (OracleComp (LazyRevealProbe.World Coordinate))))
    (computation : OracleComp spec α)
    (left right : DeferredContext → Nat → (α × SplitHashCache) → ProbComp Bool)
    (heq : ∀ context fuel value,
      context.ValuesConsistent → StartTableAgrees context.state table →
      PublishedValues context.state → CanonicalMaterializedValues table context →
      evalDist (left context fuel value) = evalDist (right context fuel value))
    (context : DeferredContext) (fuel : Nat) (cache : SplitHashCache)
    (hconsistent : context.ValuesConsistent)
    (hstarts : StartTableAgrees context.state table)
    (hpublished : PublishedValues context.state)
    (hcanonical : CanonicalMaterializedValues table context) :
    evalDist (directBoundaryObserve impl computation left context fuel table cache) =
      evalDist (directBoundaryObserve impl computation right context fuel table cache) := by
  induction computation using OracleComp.inductionOn generalizing context fuel cache with
  | pure value =>
      rw [directBoundaryObserve, OracleComp.construct_pure,
        directBoundaryObserve, OracleComp.construct_pure]
      exact heq context fuel (value, cache) hconsistent hstarts hpublished hcanonical
  | query_bind query next ih =>
      rw [directBoundaryObserve, OracleComp.construct_query_bind,
        directBoundaryObserve, OracleComp.construct_query_bind]
      apply evalDist_bind_congr
      intro result hresult
      cases result with
      | none => rfl
      | some result =>
          have hcore := resolvedCore_of_mem_runDirectResolvedFromTable
            ((impl query).run cache) context fuel table result hconsistent hstarts hresult
          unfold finishObserve canonicalizeObserve
          by_cases hnextPub : PublishedValues result.context.state
          · simp only [hnextPub, ↓reduceIte]
            exact ih result.value.1 (canonicalizeMaterializedValues table result.context)
              result.remaining result.value.2
              (canonicalizeMaterializedValues_valuesConsistent table result.context hcore.2.1)
              (canonicalizeMaterializedValues_startTableAgrees table result.context)
              hnextPub.to_canonicalizedMaterializedValues
              (canonicalizeMaterializedValues_canonical table result.context hcore.2.1)
          · simp [hnextPub]

theorem evalDist_granularVerifierFinishObserve_eq_direct
    (parameter : PublicParameter) (root : Digest)
    (table : OtsSecretIndex → HashOutput)
    (ftsSecret : Index → FtsTree → FtsLeaf → Digest)
    (context : DeferredContext) (fuel : Nat)
    (value : (Forgery × QueryLog SigningSpec) × SplitHashCache)
    (hconsistent : context.ValuesConsistent)
    (hstarts : StartTableAgrees context.state table)
    (hpublished : PublishedValues context.state)
    (hcanonical : CanonicalMaterializedValues table context) :
    evalDist (granularVerifierFinishObserve parameter root table ftsSecret context fuel value) =
      evalDist (directVerifierFinishObserve table parameter root context fuel value) := by
  rw [granularVerifierFinishObserve_eq_body, directVerifierFinishObserve_eq_body]
  exact evalDist_directBoundaryObserve_eq_flat_of_public (probingRomImpl parameter)
    (preservesPublishedValuesImpl_probingRomImpl parameter)
    (fun query coordinate => preservesCoordinateMaterializedPublished_probingRomImpl parameter coordinate query)
    _ _ context fuel table value.2 hconsistent hstarts hpublished hcanonical

theorem evalDist_granularRetainedRestObserve_eq_allDirect
    (adversary : Adversary) (parameter : PublicParameter)
    (table : OtsSecretIndex → HashOutput)
    (ftsSecret : Index → FtsTree → FtsLeaf → Digest)
    (context : DeferredContext) (fuel : Nat) (value : Digest × SplitHashCache)
    (hconsistent : context.ValuesConsistent)
    (hstarts : StartTableAgrees context.state table)
    (hpublished : PublishedValues context.state)
    (hcanonical : CanonicalMaterializedValues table context) :
    evalDist (granularRetainedRestObserve adversary parameter table ftsSecret context fuel value) =
      evalDist (allDirectRetainedRestObserve adversary parameter table ftsSecret context fuel value) := by
  unfold granularRetainedRestObserve retainedGameRestComputation
  rw [directBoundaryObserve_bind]
  change evalDist (directBoundaryObserve _ _
    (granularVerifierFinishObserve parameter value.1 table ftsSecret) context fuel table value.2) = _
  exact evalDist_directBoundaryObserve_eq_of_canonical _ _ _ _
    (fun nextContext remaining nextValue hc hs hp hk =>
      evalDist_granularVerifierFinishObserve_eq_direct parameter value.1 table ftsSecret
        nextContext remaining nextValue hc hs hp hk)
    context fuel value.2 hconsistent hstarts hpublished hcanonical

end SphincsSecurity.Concrete.OtsProbeSimulation
