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

end SphincsSecurity.Concrete.OtsProbeSimulation
