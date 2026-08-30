import SphincsSecurity.Proof.OtsProbeResolvedAdaptiveEndpoint
import SphincsSecurity.Proof.OtsProbeResolvedDirectRecursive

namespace SphincsSecurity.Concrete.OtsProbeSimulation

open OracleComp OracleSpec

attribute [local irreducible] maskedPublishedTreeRoot

noncomputable def directBoundaryObserve
    (impl : QueryImpl spec
      (StateT SplitHashCache (OracleComp (LazyRevealProbe.World Coordinate))))
    (computation : OracleComp spec α)
    (observe : DeferredContext → Nat → (α × SplitHashCache) → ProbComp Bool)
    (context : DeferredContext) (fuel : Nat)
    (table : OtsSecretIndex → HashOutput) (cache : SplitHashCache) : ProbComp Bool := by
  classical
  exact OracleComp.construct
    (C := fun _ : OracleComp spec α =>
      (DeferredContext → Nat → (α × SplitHashCache) → ProbComp Bool) →
        DeferredContext → Nat → (OtsSecretIndex → HashOutput) → SplitHashCache → ProbComp Bool)
    (fun value observe context fuel _table cache => observe context fuel (value, cache))
    (fun query _next recursivelyRun observe context fuel table cache =>
      runDirectResolvedFromTable context fuel table ((impl query).run cache) >>=
        finishObserve (canonicalizeObserve table
          (fun nextContext remaining value =>
            recursivelyRun value.1 observe nextContext remaining table value.2)))
    computation observe context fuel table cache

set_option maxRecDepth 100000 in
theorem directBoundaryObserve_dooms
    (impl : QueryImpl spec
      (StateT SplitHashCache (OracleComp (LazyRevealProbe.World Coordinate))))
    (computation : OracleComp spec α)
    (observe : DeferredContext → Nat → (α × SplitHashCache) → ProbComp Bool)
    [ObserverDooms table observe]
    (context : DeferredContext) (fuel : Nat) (cache : SplitHashCache)
    (hconsistent : context.ValuesConsistent)
    (hstarts : StartTableAgrees context.state table)
    (hdoomed : ¬DeferredCompletable table context) :
    evalDist (directBoundaryObserve impl computation observe context fuel table cache) =
      evalDist (pure true : ProbComp Bool) := by
  induction computation using OracleComp.inductionOn generalizing context fuel cache with
  | pure value =>
      rw [directBoundaryObserve, OracleComp.construct_pure]
      exact ObserverDooms.eq_true context fuel (value, cache) hconsistent hstarts hdoomed
  | query_bind query next ih =>
      rw [directBoundaryObserve, OracleComp.construct_query_bind]
      let nextObserve : DeferredContext → Nat →
          ((spec.Range query) × SplitHashCache) → ProbComp Bool :=
        fun nextContext remaining value =>
          directBoundaryObserve impl (next value.1) observe nextContext remaining table value.2
      letI : ObserverDooms table nextObserve := ⟨by
        intro nextContext remaining value hnextConsistent hnextStarts hnextDoomed
        exact ih value.1 nextContext remaining value.2 hnextConsistent hnextStarts hnextDoomed⟩
      exact evalDist_runDirectResolvedObserve_eq_true_of_not_completable_auto
        (observe := canonicalizeObserve table nextObserve) context fuel table
          ((impl query).run cache) hconsistent hstarts hdoomed

theorem valid_completable_canonicalizeMaterializedValues
    (table : OtsSecretIndex → HashOutput) (context : DeferredContext)
    (hvalid : context.Valid) (hcompletable : DeferredCompletable table context) :
    (canonicalizeMaterializedValues table context).Valid ∧
      DeferredCompletable table (canonicalizeMaterializedValues table context) := by
  obtain ⟨completion, hcompletion⟩ := hcompletable
  have hclean : ∀ coordinate output,
      resolvedCompletionValue table context coordinate = some output →
        ¬context.state.hitAt coordinate output := by
    intro coordinate output hvalue hhit
    have houtput := hcompletion.eq_resolvedCompletionValue coordinate output hvalue
    unfold LazyRevealProbe.State.hitAt at hhit
    rw [LazyRevealProbe.State.mem_pendingAt_iff] at hhit
    exact hcompletion.2.2.1 coordinate (truncateHash output) hhit (by rw [houtput])
  exact ⟨canonicalizeMaterializedValues_valid table context hvalid hclean,
    ⟨completion, hcompletion.to_canonicalizedMaterializedValues⟩⟩

theorem canonicalizeMaterializedValues_chain_value
    (table : OtsSecretIndex → HashOutput) (context : DeferredContext)
    (hstarts : StartTableAgrees context.state table)
    (hchainValid : ChainState.ValidFor allowed context.state)
    (coordinate : Coordinate) (hchain : IsChainCoordinate coordinate) :
    (canonicalizeMaterializedValues table context).state.values coordinate =
      context.state.values coordinate := by
  unfold canonicalizeMaterializedValues publicMaterializedValues
  cases hvalue : context.state.values coordinate with
  | none =>
      have hnotRevealed : coordinate ∉ context.state.revealed := by
        intro hrevealed
        exact (hchainValid coordinate hchain).2.1 hrevealed hvalue
      simp [hnotRevealed]
  | some output =>
      have hrevealed : coordinate ∈ context.state.revealed :=
        (hchainValid coordinate hchain).1 (by simp [hvalue])
      simp only [hrevealed, ↓reduceIte]
      cases coordinate with
      | chainStart lay tree leafIdx chainIdx =>
          let index : OtsSecretIndex := ⟨lay, tree, leafIdx, chainIdx⟩
          have htable : output = table index := hstarts index output (by
            simpa [index, OtsSecretIndex.coordinate] using hvalue)
          simp [resolvedCompletionValue, index, htable]
      | position position =>
          simp [resolvedCompletionValue, DeferredContext.positionValue, hvalue]

theorem canonicalizeMaterializedValues_chain_private_eq
    (table : OtsSecretIndex → HashOutput) (context : DeferredContext)
    (hdirect : context = directDeferredContext context.state)
    (hstarts : StartTableAgrees context.state table)
    (hchainValid : ChainState.ValidFor allowed context.state)
    (lay : Layer) (tree : TreeIndex) (leafIdx : LeafIndex)
    (chainIdx : ChainIndex) (step : ChainStep) :
    (canonicalizeMaterializedValues table context).values
        (.chain lay tree leafIdx chainIdx step) =
      (canonicalizeMaterializedValues table context).state.values
        (.position (.chain lay tree leafIdx chainIdx step)) := by
  have hprivate :
      context.values (.chain lay tree leafIdx chainIdx step) =
        context.state.values (.position (.chain lay tree leafIdx chainIdx step)) := by
    rw [hdirect]
    rfl
  change context.values (.chain lay tree leafIdx chainIdx step) = _
  rw [canonicalizeMaterializedValues_chain_value table context hstarts hchainValid]
  · exact hprivate
  · trivial

theorem ChainValuesMirrored.canonicalizeMaterializedValues
    {context : DeferredContext} (hmirror : ChainValuesMirrored context)
    (table : OtsSecretIndex → HashOutput)
    (hstarts : StartTableAgrees context.state table)
    (hchainValid : ChainState.ValidFor allowed context.state) :
    ChainValuesMirrored (canonicalizeMaterializedValues table context) := by
  intro lay tree leafIdx chainIdx step
  change context.values (.chain lay tree leafIdx chainIdx step) = _
  rw [canonicalizeMaterializedValues_chain_value table context hstarts hchainValid]
  · exact hmirror lay tree leafIdx chainIdx step
  · trivial

theorem ChainState.ValidFor.canonicalizeMaterializedValues
    {context : DeferredContext} (hvalid : ChainState.ValidFor allowed context.state)
    (table : OtsSecretIndex → HashOutput)
    (hstarts : StartTableAgrees context.state table) :
    ChainState.ValidFor allowed
      (canonicalizeMaterializedValues table context).state := by
  intro coordinate hchain
  rw [canonicalizeMaterializedValues_chain_value table context hstarts hvalid coordinate hchain,
    canonicalizeMaterializedValues_revealed]
  exact hvalid coordinate hchain

theorem ChainInvariant.canonicalizeMaterializedValues
    (table : OtsSecretIndex → HashOutput) (context : DeferredContext)
    (hstarts : StartTableAgrees context.state table)
    (hinvariant : ChainInvariant parameter allowed context.state cache) :
    ChainInvariant parameter allowed
      (canonicalizeMaterializedValues table context).state cache := by
  constructor
  · intro coordinate hchain
    have hcoordinate := hinvariant.1 coordinate hchain
    rw [canonicalizeMaterializedValues_chain_value table context hstarts hinvariant.1
      coordinate hchain, canonicalizeMaterializedValues_revealed]
    exact hcoordinate
  · intro probe input hmatches hcached hnotAllowed
    have hpending := hinvariant.2 probe input hmatches hcached hnotAllowed
    simpa [LazyRevealProbe.State.pendingAt,
      canonicalizeMaterializedValues_pending] using hpending

theorem preservesChainValid_maskedSignAfterDigest_true
    (parameter : PublicParameter)
    (ftsSecret : Index → FtsTree → FtsLeaf → Digest)
    (randomness : Randomness) (index : Index) (leaves : DigestTree → FtsLeaf) :
    PreservesChainValid (fun _ => True)
      (maskedSignAfterDigest parameter ftsSecret randomness index leaves) := by
  unfold maskedSignAfterDigest
  apply ((preservesChainValidImpl_ordinaryHashImpl (fun _ => True)).simulateQ
    (ftsOpen parameter index leaves (ftsSecret index))).bind
  intro _ftsPath
  apply (preservesChainValid_sequenceFin (fun _ => True) _ fun lay =>
    preservesChainValid_maskedSignLayer (fun _ => True) parameter ftsSecret index lay).bind
  intro layers
  cases hparts : traverseOption layers with
  | none =>
      simp only
      exact preservesChainValid_pure (fun _ => True) none
  | some parts =>
      simp only
      apply (preservesChainValid_sequenceFin (fun _ => True) _ fun lay =>
        preservesChainValid_revealLayerValues (fun _ => True) index lay (parts lay).2
          (fun _ => trivial)).bind
      intro _revealed
      exact preservesChainValid_pure (fun _ => True) _

theorem preservesChainValid_maskedSign_true
    (parameter : PublicParameter) (root : Digest)
    (ftsSecret : Index → FtsTree → FtsLeaf → Digest) (message : Message) :
    PreservesChainValid (fun _ => True) (maskedSign parameter root ftsSecret message) := by
  unfold maskedSign
  apply ((preservesChainValidImpl_ordinaryRomImpl (fun _ => True)).simulateQ
    (signDigestLoop digestAttemptLimit
      (⟨parameter, root, fun _ _ _ _ => 0, ftsSecret⟩ : SecretKey) message)).bind
  intro selected
  cases selected with
  | none => exact preservesChainValid_pure (fun _ => True) none
  | some data =>
      exact preservesChainValid_maskedSignAfterDigest_true parameter ftsSecret
        data.1 data.2.1 data.2.2

theorem preservesChainValidImpl_maskedExpandedAdversaryImpl_true
    (parameter : PublicParameter) (root : Digest)
    (ftsSecret : Index → FtsTree → FtsLeaf → Digest) :
    PreservesChainValidImpl (fun _ => True)
      (maskedExpandedAdversaryImpl parameter root ftsSecret) := by
  intro query
  cases query with
  | inl query =>
      exact preservesChainValidImpl_probingRomImpl (fun _ => True)
        (by intro candidate _hallowed _hchain; trivial) parameter query
  | inr message =>
      exact preservesChainValid_maskedSign_true parameter root ftsSecret message

theorem preservesChainValid_publishCoordinate_of_not_chain
    (allowed : Coordinate → Prop) (coordinate : Coordinate)
    (hnotChain : ¬IsChainCoordinate coordinate) :
    PreservesChainValid allowed (publishCoordinate coordinate) := by
  intro state cache fuel finalState remaining value finalCache hvalid hresult
  unfold publishCoordinate at hresult
  change LazyRevealProbe.RawResult.done finalState remaining (value, finalCache) ∈
    support (LazyRevealProbe.runRaw state fuel
      (LazyRevealProbe.publishQuery coordinate >>= fun output => pure (output, cache))) at hresult
  rw [LazyRevealProbe.publishQuery, LazyRevealProbe.runRaw_publish_query_bind] at hresult
  simp [LazyRevealProbe.runRaw] at hresult
  rcases hresult with ⟨rfl, rfl, rfl, rfl⟩
  intro other hchain
  have hne : other ≠ coordinate := by
    intro heq
    exact hnotChain (heq ▸ hchain)
  simpa [LazyRevealProbe.State.publish, hne] using hvalid other hchain

theorem preservesChainValid_maskedPublishedTreeRoot_true :
    PreservesChainValid (fun _ => True) maskedPublishedTreeRoot := by
  rw [maskedPublishedTreeRoot_eq]
  apply (preservesChainValid_maskedTreeRoot (fun _ => True) topLayer rootTree).bind
  intro root
  apply (preservesChainValid_publishCoordinate_of_not_chain (fun _ => True)
    (.position (.node topLayer rootTree
      ⟨layerHeight topLayer - 1, by norm_num [layerHeight, topLayer, maxLayerHeight]⟩ 0))
    (by simp [IsChainCoordinate])).bind
  intro _
  exact preservesChainValid_pure (fun _ => True) root

theorem preservesChainValid_canonicalVerifierFinish_true
    (parameter : PublicParameter) (root : Digest)
    (forgeryLog : Forgery × QueryLog SigningSpec) :
    PreservesChainValid (fun _ => True)
      (canonicalVerifierFinish parameter root forgeryLog) := by
  unfold canonicalVerifierFinish
  exact ((preservesChainValidImpl_probingRomImpl (fun _ => True)
    (by intro candidate _hallowed _hchain; trivial) parameter).simulateQ
      (scheme.verify ⟨root, parameter⟩ forgeryLog.1.message forgeryLog.1.signature)).bind
        fun _ => preservesChainValid_pure (fun _ => True) _

set_option maxRecDepth 100000 in
theorem evalDist_directBoundaryObserve_eq_of_chain_invariants
    (impl : QueryImpl spec
      (StateT SplitHashCache (OracleComp (LazyRevealProbe.World Coordinate))))
    (himpl : PreservesChainValidImpl (fun _ => True) impl)
    (computation : OracleComp spec α)
    (left right : DeferredContext → Nat → (α × SplitHashCache) → ProbComp Bool)
    (heq : ∀ context fuel value,
      context.ValuesConsistent → StartTableAgrees context.state table →
      ChainValuesMirrored context → ChainState.ValidFor (fun _ => True) context.state →
      evalDist (left context fuel value) = evalDist (right context fuel value))
    (context : DeferredContext) (fuel : Nat) (cache : SplitHashCache)
    (hconsistent : context.ValuesConsistent)
    (hstarts : StartTableAgrees context.state table)
    (hmirror : ChainValuesMirrored context)
    (hchainValid : ChainState.ValidFor (fun _ => True) context.state) :
    evalDist (directBoundaryObserve impl computation left context fuel table cache) =
      evalDist (directBoundaryObserve impl computation right context fuel table cache) := by
  induction computation using OracleComp.inductionOn generalizing context fuel cache with
  | pure value =>
      rw [directBoundaryObserve, OracleComp.construct_pure,
        directBoundaryObserve, OracleComp.construct_pure]
      exact heq context fuel (value, cache) hconsistent hstarts hmirror hchainValid
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
          have hnextMirror := chainValuesMirrored_of_mem_runDirectResolvedFromTable
            ((impl query).run cache) context fuel table result hmirror hresult
          have hnextChainValid := chainValid_of_mem_runDirectResolvedFromTable
            (fun _ => True) (impl query) context fuel table cache result (himpl query)
              hchainValid hresult
          unfold finishObserve canonicalizeObserve
          by_cases hpublished : PublishedValues result.context.state
          · simp only [hpublished, ↓reduceIte]
            have hcanonicalConsistent :=
              canonicalizeMaterializedValues_valuesConsistent table result.context hcore.2.1
            have hcanonicalStarts :=
              canonicalizeMaterializedValues_startTableAgrees table result.context
            have hcanonicalMirror := hnextMirror.canonicalizeMaterializedValues table hcore.2.2
              hnextChainValid
            have hcanonicalChainValid := hnextChainValid.canonicalizeMaterializedValues table
              hcore.2.2
            exact ih result.value.1 (canonicalizeMaterializedValues table result.context)
              result.remaining result.value.2 hcanonicalConsistent hcanonicalStarts
                hcanonicalMirror hcanonicalChainValid
          · simp [hpublished]

set_option maxRecDepth 100000 in
theorem evalDist_boundaryObserve_eq_directBoundaryObserve
    (impl : QueryImpl spec
      (StateT SplitHashCache (OracleComp (LazyRevealProbe.World Coordinate))))
    (computation : OracleComp spec α)
    (observe : DeferredContext → Nat → (α × SplitHashCache) → ProbComp Bool)
    [ObserverDooms table observe] [ObserverSynchronized table observe]
    [ObserverPositionNeutral table observe]
    (context : DeferredContext) (fuel : Nat) (cache : SplitHashCache)
    (hvalid : context.Valid) (hcompletable : DeferredCompletable table context) :
    evalDist (boundaryObserve impl computation observe context fuel table cache) =
      evalDist (directBoundaryObserve impl computation observe context fuel table cache) := by
  induction computation using OracleComp.inductionOn generalizing context fuel cache with
  | pure value =>
      rw [boundaryObserve, OracleComp.construct_pure,
        directBoundaryObserve, OracleComp.construct_pure]
  | query_bind query next ih =>
      rw [boundaryObserve, OracleComp.construct_query_bind,
        directBoundaryObserve, OracleComp.construct_query_bind]
      let leftNext : DeferredContext → Nat →
          ((spec.Range query) × SplitHashCache) → ProbComp Bool :=
        fun nextContext remaining value =>
          boundaryObserve impl (next value.1) observe nextContext remaining table value.2
      let rightNext : DeferredContext → Nat →
          ((spec.Range query) × SplitHashCache) → ProbComp Bool :=
        fun nextContext remaining value =>
          directBoundaryObserve impl (next value.1) observe nextContext remaining table value.2
      letI : ObserverDooms table leftNext := ⟨by
        intro nextContext remaining value hconsistent hstarts hdoomed
        exact boundaryObserve_dooms impl (next value.1) observe nextContext remaining value.2
          hconsistent hstarts hdoomed⟩
      letI : ObserverSynchronized table leftNext := ⟨by
        intro left right remaining value hcontext hvalues hrevealed
        exact boundaryObserve_synchronized impl (next value.1) observe left right remaining
          value.2 hcontext hvalues hrevealed⟩
      letI : ObserverPositionNeutral table leftNext := ⟨by
        intro position nextContext remaining value hnextValid hnextCompletable hensured
        exact boundaryObserve_positionNeutral impl (next value.1) observe position nextContext
          remaining value.2 hnextValid hnextCompletable hensured⟩
      calc
        _ = evalDist (runDirectResolvedObserve (canonicalizeObserve table leftNext)
              context fuel table ((impl query).run cache)) :=
          evalDist_runResolvedObserve_eq_runDirectResolvedObserve
            (observe := canonicalizeObserve table leftNext) context fuel table
              ((impl query).run cache) hvalid hcompletable
        _ = _ := by
          unfold runDirectResolvedObserve
          apply evalDist_bind_congr
          intro result hresult
          cases result with
          | none => rfl
          | some result =>
              have hcore := resolvedCore_of_mem_runDirectResolvedFromTable
                ((impl query).run cache) context fuel table result hvalid.valuesConsistent
                  (startTableAgrees_of_deferredCompletable hcompletable) hresult
              change evalDist (canonicalizeObserve table leftNext result.context
                result.remaining result.value) =
                evalDist (canonicalizeObserve table rightNext result.context
                  result.remaining result.value)
              by_cases hnextCompletable : DeferredCompletable table result.context
              · have hnextValid := valid_of_resolvedCore_completable table result.context
                  hcore.2.1 hcore.2.2 hnextCompletable
                unfold canonicalizeObserve
                by_cases hpublished : PublishedValues result.context.state
                · simp only [hpublished, ↓reduceIte]
                  have hcanonical := valid_completable_canonicalizeMaterializedValues table
                    result.context hnextValid hnextCompletable
                  exact ih result.value.1 (canonicalizeMaterializedValues table result.context)
                    result.remaining result.value.2 hcanonical.1 hcanonical.2
                · simp [hpublished]
              · have hdoomed : DoomedResolvedContext table result.context :=
                  ⟨hcore.2.1, hcore.2.2, hnextCompletable⟩
                unfold canonicalizeObserve
                by_cases hpublished : PublishedValues result.context.state
                · simp only [hpublished, ↓reduceIte]
                  have hcanonical := doomedResolvedContext_canonicalizeMaterializedValues
                    hdoomed
                  exact (boundaryObserve_dooms impl (next result.value.1) observe
                    (canonicalizeMaterializedValues table result.context) result.remaining
                      result.value.2 hcanonical.1 hcanonical.2.1 hcanonical.2.2).trans
                    (directBoundaryObserve_dooms impl (next result.value.1) observe
                      (canonicalizeMaterializedValues table result.context) result.remaining
                        result.value.2 hcanonical.1 hcanonical.2.1 hcanonical.2.2).symm
                · simp [hpublished]

set_option maxRecDepth 100000 in
theorem directBoundaryObserve_synchronized
    (impl : QueryImpl spec
      (StateT SplitHashCache (OracleComp (LazyRevealProbe.World Coordinate))))
    (computation : OracleComp spec α)
    (observe : DeferredContext → Nat → (α × SplitHashCache) → ProbComp Bool)
    [ObserverDooms table observe] [ObserverSynchronized table observe]
    [ObserverPositionNeutral table observe]
    (left right : DeferredContext) (fuel : Nat) (cache : SplitHashCache)
    (hcontext : FinalizationContextEq table (some left) (some right))
    (hvalues : left.state.values = right.state.values)
    (hrevealed : left.state.revealed = right.state.revealed) :
    evalDist (directBoundaryObserve impl computation observe left fuel table cache) =
      evalDist (directBoundaryObserve impl computation observe right fuel table cache) := by
  rcases hcontext with ⟨hview, hleftValid, hrightValid, hleftCompletable⟩
  have hrightCompletable : DeferredCompletable table right := by
    rcases hleftCompletable with ⟨completion, hcompletion⟩
    exact ⟨completion, (hview.deferredCompletion_iff completion).mp hcompletion⟩
  calc
    _ = evalDist (boundaryObserve impl computation observe left fuel table cache) :=
      (evalDist_boundaryObserve_eq_directBoundaryObserve impl computation observe left fuel
        cache hleftValid hleftCompletable).symm
    _ = evalDist (boundaryObserve impl computation observe right fuel table cache) :=
      boundaryObserve_synchronized impl computation observe left right fuel cache
        ⟨hview, hleftValid, hrightValid, hleftCompletable⟩ hvalues hrevealed
    _ = _ := evalDist_boundaryObserve_eq_directBoundaryObserve impl computation observe right
      fuel cache hrightValid hrightCompletable

set_option maxRecDepth 100000 in
theorem directBoundaryObserve_positionNeutral
    (impl : QueryImpl spec
      (StateT SplitHashCache (OracleComp (LazyRevealProbe.World Coordinate))))
    (computation : OracleComp spec α)
    (observe : DeferredContext → Nat → (α × SplitHashCache) → ProbComp Bool)
    [ObserverDooms table observe] [ObserverSynchronized table observe]
    [ObserverPositionNeutral table observe]
    (position : Position) (context : DeferredContext) (fuel : Nat)
    (cache : SplitHashCache)
    (hvalid : context.Valid) (hcompletable : DeferredCompletable table context)
    (hensured : Coordinate.position position ∈ context.state.ensured) :
    evalDist (resolveDeferredPositionValue position context >>= fun resolved =>
      match resolved with
      | none => pure true
      | some resolved =>
          directBoundaryObserve impl computation observe resolved.toDeferredContext fuel table
            cache) =
      evalDist (directBoundaryObserve impl computation observe context fuel table cache) := by
  calc
    _ = evalDist (resolveDeferredPositionValue position context >>= fun resolved =>
        match resolved with
        | none => pure true
        | some resolved =>
            boundaryObserve impl computation observe resolved.toDeferredContext fuel table
              cache) := by
      apply evalDist_bind_congr
      intro resolved hresolved
      cases resolved with
      | none => rfl
      | some resolved =>
          have hresolvedValid := hvalid.of_resolveDeferredPositionValue position resolved
            hresolved
          have hresolvedCompletable := hcompletable.of_resolveDeferredPositionValue hvalid
            position resolved hresolved
          simpa using (evalDist_boundaryObserve_eq_directBoundaryObserve impl computation observe
            resolved.toDeferredContext fuel cache hresolvedValid hresolvedCompletable).symm
    _ = evalDist (boundaryObserve impl computation observe context fuel table cache) :=
      boundaryObserve_positionNeutral impl computation observe position context fuel cache
        hvalid hcompletable hensured
    _ = _ := evalDist_boundaryObserve_eq_directBoundaryObserve impl computation observe context
      fuel cache hvalid hcompletable

noncomputable def directBoundaryDeferredRetainedFinishIsNone
    (adversary : Adversary) (parameter : PublicParameter)
    (table : OtsSecretIndex → HashOutput)
    (ftsSecret : Index → FtsTree → FtsLeaf → Digest) (fuel : Nat) :
    ProbComp Bool := do
  let rootResult ← runResolvedFromTable
    { state := (LazyRevealProbe.State.empty : LazyRevealProbe.State Coordinate)
      values := emptyDeferredStructuralValues }
    fuel table (maskedPublishedTreeRoot.run emptySplitHashCache)
  match rootResult with
  | none => pure true
  | some rootResult =>
      directBoundaryObserve (maskedExpandedAdversaryImpl parameter rootResult.value.1 ftsSecret)
        (signingTraceComputation (adversary.main ⟨rootResult.value.1, parameter⟩))
        (verifierFinishObserve table parameter rootResult.value.1)
        rootResult.context rootResult.remaining table rootResult.value.2

set_option maxRecDepth 100000 in
theorem evalDist_boundaryDeferredRetainedFinishIsNone_eq_direct
    (adversary : Adversary) (parameter : PublicParameter)
    (table : OtsSecretIndex → HashOutput)
    (ftsSecret : Index → FtsTree → FtsLeaf → Digest) (fuel : Nat) :
    evalDist (boundaryDeferredRetainedFinishIsNone adversary parameter table ftsSecret fuel) =
      evalDist (directBoundaryDeferredRetainedFinishIsNone adversary parameter table ftsSecret
        fuel) := by
  unfold boundaryDeferredRetainedFinishIsNone
    directBoundaryDeferredRetainedFinishIsNone
  apply evalDist_bind_congr
  intro rootOption hroot
  cases rootOption with
  | none => rfl
  | some rootResult =>
      have hrootInvariants : rootResult.context.Valid ∧
          DeferredCompletable table rootResult.context :=
        valid_completable_of_mem_runResolvedFromTable_of_finalizationMaterializedCouples
          (α := Digest) table maskedPublishedTreeRoot
          (finalizationMaterializedCouples_maskedPublishedTreeRoot table)
          { state := (LazyRevealProbe.State.empty : LazyRevealProbe.State Coordinate)
            values := emptyDeferredStructuralValues }
          fuel emptySplitHashCache rootResult DeferredContext.valid_empty
            (deferredCompletable_empty table) hroot
      exact evalDist_boundaryObserve_eq_directBoundaryObserve
        (maskedExpandedAdversaryImpl parameter rootResult.value.1 ftsSecret)
        (signingTraceComputation (adversary.main ⟨rootResult.value.1, parameter⟩))
        (verifierFinishObserve table parameter rootResult.value.1)
        rootResult.context rootResult.remaining rootResult.value.2
          hrootInvariants.1 hrootInvariants.2

noncomputable def directRetainedRestObserve
    (adversary : Adversary) (parameter : PublicParameter)
    (table : OtsSecretIndex → HashOutput)
    (ftsSecret : Index → FtsTree → FtsLeaf → Digest)
    (context : DeferredContext) (fuel : Nat)
    (value : Digest × SplitHashCache) : ProbComp Bool :=
  directBoundaryObserve (maskedExpandedAdversaryImpl parameter value.1 ftsSecret)
    (signingTraceComputation (adversary.main ⟨value.1, parameter⟩))
    (verifierFinishObserve table parameter value.1)
    context fuel table value.2

instance directRetainedRestObserve_observerDooms
    (adversary : Adversary) (parameter : PublicParameter)
    (table : OtsSecretIndex → HashOutput)
    (ftsSecret : Index → FtsTree → FtsLeaf → Digest) :
    ObserverDooms table
      (directRetainedRestObserve adversary parameter table ftsSecret) where
  eq_true context fuel value hconsistent hstarts hdoomed := by
    exact directBoundaryObserve_dooms
      (maskedExpandedAdversaryImpl parameter value.1 ftsSecret)
      (signingTraceComputation (adversary.main ⟨value.1, parameter⟩))
      (verifierFinishObserve table parameter value.1)
      context fuel value.2 hconsistent hstarts hdoomed

instance directRetainedRestObserve_observerSynchronized
    (adversary : Adversary) (parameter : PublicParameter)
    (table : OtsSecretIndex → HashOutput)
    (ftsSecret : Index → FtsTree → FtsLeaf → Digest) :
    ObserverSynchronized table
      (directRetainedRestObserve adversary parameter table ftsSecret) where
  eq_of_synchronized left right fuel value hcontext hvalues hrevealed := by
    exact directBoundaryObserve_synchronized
      (maskedExpandedAdversaryImpl parameter value.1 ftsSecret)
      (signingTraceComputation (adversary.main ⟨value.1, parameter⟩))
      (verifierFinishObserve table parameter value.1)
      left right fuel value.2 hcontext hvalues hrevealed

instance directRetainedRestObserve_observerPositionNeutral
    (adversary : Adversary) (parameter : PublicParameter)
    (table : OtsSecretIndex → HashOutput)
    (ftsSecret : Index → FtsTree → FtsLeaf → Digest) :
    ObserverPositionNeutral table
      (directRetainedRestObserve adversary parameter table ftsSecret) where
  eq_resolve position context fuel value hvalid hcompletable hensured := by
    exact directBoundaryObserve_positionNeutral
      (maskedExpandedAdversaryImpl parameter value.1 ftsSecret)
      (signingTraceComputation (adversary.main ⟨value.1, parameter⟩))
      (verifierFinishObserve table parameter value.1)
      position context fuel value.2 hvalid hcompletable hensured

noncomputable def fullyDirectBoundaryDeferredRetainedFinishIsNone
    (adversary : Adversary) (parameter : PublicParameter)
    (table : OtsSecretIndex → HashOutput)
    (ftsSecret : Index → FtsTree → FtsLeaf → Digest) (fuel : Nat) :
    ProbComp Bool :=
  runDirectResolvedObserve (directRetainedRestObserve adversary parameter table ftsSecret)
    { state := (LazyRevealProbe.State.empty : LazyRevealProbe.State Coordinate)
      values := emptyDeferredStructuralValues }
    fuel table (maskedPublishedTreeRoot.run emptySplitHashCache)

set_option maxRecDepth 100000 in
theorem evalDist_directBoundaryDeferredRetainedFinishIsNone_eq_fullyDirect
    (adversary : Adversary) (parameter : PublicParameter)
    (table : OtsSecretIndex → HashOutput)
    (ftsSecret : Index → FtsTree → FtsLeaf → Digest) (fuel : Nat) :
    evalDist (directBoundaryDeferredRetainedFinishIsNone adversary parameter table ftsSecret
        fuel) =
      evalDist (fullyDirectBoundaryDeferredRetainedFinishIsNone adversary parameter table
        ftsSecret fuel) := by
  let context : DeferredContext :=
    { state := (LazyRevealProbe.State.empty : LazyRevealProbe.State Coordinate)
      values := emptyDeferredStructuralValues }
  have hleft : directBoundaryDeferredRetainedFinishIsNone adversary parameter table ftsSecret
      fuel = runResolvedObserve
        (directRetainedRestObserve adversary parameter table ftsSecret)
        context fuel table (maskedPublishedTreeRoot.run emptySplitHashCache) := by
    unfold directBoundaryDeferredRetainedFinishIsNone runResolvedObserve
    apply bind_congr
    intro result
    cases result <;> rfl
  rw [hleft]
  exact evalDist_runResolvedObserve_eq_runDirectResolvedObserve
    (observe := directRetainedRestObserve adversary parameter table ftsSecret)
    context fuel table (maskedPublishedTreeRoot.run emptySplitHashCache)
      DeferredContext.valid_empty (deferredCompletable_empty table)

noncomputable def directVerifierFinishObserve
    (table : OtsSecretIndex → HashOutput)
    (parameter : PublicParameter) (root : Digest)
    (context : DeferredContext) (fuel : Nat)
    (value : (Forgery × QueryLog SigningSpec) × SplitHashCache) : ProbComp Bool :=
  runDirectResolvedFromTable context fuel table
      ((canonicalVerifierFinish parameter root value.1).run value.2) >>=
    finishObserve (resolvedFinalizationObserve table)

theorem evalDist_verifierFinishObserve_eq_direct
    (table : OtsSecretIndex → HashOutput)
    (parameter : PublicParameter) (root : Digest)
    (context : DeferredContext) (fuel : Nat)
    (value : (Forgery × QueryLog SigningSpec) × SplitHashCache)
    (hconsistent : context.ValuesConsistent)
    (hstarts : StartTableAgrees context.state table) :
    evalDist (verifierFinishObserve table parameter root context fuel value) =
      evalDist (directVerifierFinishObserve table parameter root context fuel value) := by
  by_cases hcompletable : DeferredCompletable table context
  · have hvalid := valid_of_resolvedCore_completable table context hconsistent hstarts
      hcompletable
    exact evalDist_runResolvedFinishIsNone_eq_runDirectResolvedFinalizationIsNone
      context fuel table ((canonicalVerifierFinish parameter root value.1).run value.2)
        hvalid hcompletable
  · calc
      _ = evalDist (pure true : ProbComp Bool) :=
        ObserverDooms.eq_true context fuel value hconsistent hstarts hcompletable
      _ = _ := (evalDist_runDirectResolvedObserve_eq_true_of_not_completable_auto
        (observe := resolvedFinalizationObserve table) context fuel table
          ((canonicalVerifierFinish parameter root value.1).run value.2)
            hconsistent hstarts hcompletable).symm

noncomputable def allDirectRetainedRestObserve
    (adversary : Adversary) (parameter : PublicParameter)
    (table : OtsSecretIndex → HashOutput)
    (ftsSecret : Index → FtsTree → FtsLeaf → Digest)
    (context : DeferredContext) (fuel : Nat)
    (value : Digest × SplitHashCache) : ProbComp Bool :=
  directBoundaryObserve (maskedExpandedAdversaryImpl parameter value.1 ftsSecret)
    (signingTraceComputation (adversary.main ⟨value.1, parameter⟩))
    (directVerifierFinishObserve table parameter value.1)
    context fuel table value.2

noncomputable def allDirectBoundaryDeferredRetainedFinishIsNone
    (adversary : Adversary) (parameter : PublicParameter)
    (table : OtsSecretIndex → HashOutput)
    (ftsSecret : Index → FtsTree → FtsLeaf → Digest) (fuel : Nat) :
    ProbComp Bool :=
  runDirectResolvedObserve
    (allDirectRetainedRestObserve adversary parameter table ftsSecret)
    { state := (LazyRevealProbe.State.empty : LazyRevealProbe.State Coordinate)
      values := emptyDeferredStructuralValues }
    fuel table (maskedPublishedTreeRoot.run emptySplitHashCache)

set_option linter.constructorNameAsVariable false in
set_option maxHeartbeats 1000000 in
set_option maxRecDepth 100000 in
theorem evalDist_fullyDirectBoundaryDeferredRetainedFinishIsNone_eq_allDirect
    (adversary : Adversary) (parameter : PublicParameter)
    (table : OtsSecretIndex → HashOutput)
    (ftsSecret : Index → FtsTree → FtsLeaf → Digest) (fuel : Nat) :
    evalDist (fullyDirectBoundaryDeferredRetainedFinishIsNone adversary parameter table
        ftsSecret fuel) =
      evalDist (allDirectBoundaryDeferredRetainedFinishIsNone adversary parameter table
        ftsSecret fuel) := by
  unfold fullyDirectBoundaryDeferredRetainedFinishIsNone
    allDirectBoundaryDeferredRetainedFinishIsNone runDirectResolvedObserve
  apply evalDist_bind_congr
  intro rootOption hroot
  cases rootOption with
  | none => rfl
  | some rootResult =>
      let initial : DeferredContext :=
        { state := (LazyRevealProbe.State.empty : LazyRevealProbe.State Coordinate)
          values := emptyDeferredStructuralValues }
      generalize hrootComputation : maskedPublishedTreeRoot.run emptySplitHashCache =
        rootComputation at hroot
      change some rootResult ∈ support (runDirectResolvedFromTable initial fuel table
        rootComputation) at hroot
      have hinitialConsistent : initial.ValuesConsistent := by
        exact DeferredContext.valid_empty.valuesConsistent
      have hinitialStarts : StartTableAgrees initial.state table := by
        exact startTableAgrees_empty table
      have hcore : rootResult.table = table ∧ rootResult.context.ValuesConsistent ∧
          StartTableAgrees rootResult.context.state table := by
        exact resolvedCore_of_mem_runDirectResolvedFromTable
          (computation := rootComputation)
          (context := initial) (fuel := fuel) (table := table) (result := rootResult)
          hinitialConsistent hinitialStarts hroot
      have hmirror := chainValuesMirrored_of_mem_runDirectResolvedFromTable
        (computation := rootComputation)
        (context := initial) (fuel := fuel) (table := table) (result := rootResult)
        (by
          intro lay tree leafIdx chainIdx step
          rfl)
        hroot
      have hraw := raw_done_of_mem_runDirectResolvedFromTable rootComputation initial fuel table
        rootResult hroot
      have hrawRoot : LazyRevealProbe.RawResult.done rootResult.context.state
          rootResult.remaining rootResult.value ∈ support (LazyRevealProbe.runRaw
            (LazyRevealProbe.State.empty : LazyRevealProbe.State Coordinate) fuel
              (maskedPublishedTreeRoot.run emptySplitHashCache)) := by
        rw [hrootComputation]
        exact hraw
      generalize hrootProgram : maskedPublishedTreeRoot = rootProgram at hrawRoot
      have hpreserves : PreservesChainValid (fun _ => True) rootProgram := by
        rw [← hrootProgram]
        exact preservesChainValid_maskedPublishedTreeRoot_true
      unfold PreservesChainValid at hpreserves
      have hchainValid : ChainState.ValidFor (fun _ => True) rootResult.context.state := by
        exact hpreserves
          (LazyRevealProbe.State.empty : LazyRevealProbe.State Coordinate) emptySplitHashCache fuel
            rootResult.context.state rootResult.remaining rootResult.value.1 rootResult.value.2
              (ChainState.validFor_empty (fun _ => True)) hrawRoot
      exact evalDist_directBoundaryObserve_eq_of_chain_invariants
        (maskedExpandedAdversaryImpl parameter rootResult.value.1 ftsSecret)
        (preservesChainValidImpl_maskedExpandedAdversaryImpl_true parameter
          rootResult.value.1 ftsSecret)
        (signingTraceComputation (adversary.main ⟨rootResult.value.1, parameter⟩))
        (verifierFinishObserve table parameter rootResult.value.1)
        (directVerifierFinishObserve table parameter rootResult.value.1)
        (by
          intro context remaining value hconsistent hstarts _hmirror _hchainValid
          exact evalDist_verifierFinishObserve_eq_direct table parameter rootResult.value.1
            context remaining value hconsistent hstarts)
        rootResult.context rootResult.remaining rootResult.value.2 hcore.2.1 hcore.2.2
          hmirror hchainValid

theorem evalDist_canonicalDeferredRetainedFinishIsNone_eq_allDirect
    (adversary : Adversary) (parameter : PublicParameter)
    (table : OtsSecretIndex → HashOutput)
    (ftsSecret : Index → FtsTree → FtsLeaf → Digest) (fuel : Nat) :
    evalDist
        (canonicalDeferredRetainedRunAfterFtsSecrets adversary parameter table ftsSecret fuel >>=
          finishResolvedRunIsNone) =
      evalDist (allDirectBoundaryDeferredRetainedFinishIsNone adversary parameter table
        ftsSecret fuel) := by
  calc
    _ = evalDist
        (boundaryDeferredRetainedFinishIsNone adversary parameter table ftsSecret fuel) :=
      evalDist_canonicalDeferredRetainedFinishIsNone_eq_boundary adversary parameter table
        ftsSecret fuel
    _ = evalDist
        (directBoundaryDeferredRetainedFinishIsNone adversary parameter table ftsSecret fuel) :=
      evalDist_boundaryDeferredRetainedFinishIsNone_eq_direct adversary parameter table ftsSecret
        fuel
    _ = evalDist
        (fullyDirectBoundaryDeferredRetainedFinishIsNone adversary parameter table ftsSecret
          fuel) :=
      evalDist_directBoundaryDeferredRetainedFinishIsNone_eq_fullyDirect adversary parameter
        table ftsSecret fuel
    _ = _ := evalDist_fullyDirectBoundaryDeferredRetainedFinishIsNone_eq_allDirect adversary
      parameter table ftsSecret fuel

end SphincsSecurity.Concrete.OtsProbeSimulation
