import SphincsSecurity.Proof.OtsProbeResolvedAdaptiveObserver

/-!
# Adaptive delayed-signer bridge

The delayed signer is erased under an arbitrary terminal observer that treats doomed contexts as
failure, respects synchronized finalization views, and is neutral to an ensured private position.
The resulting clean interpreter canonicalizes materialized values only at outer-query boundaries.
-/

namespace SphincsSecurity.Concrete.OtsProbeSimulation

open OracleComp

attribute [local irreducible] maskedSignLayer

theorem evalDist_runDeferredChronologicalLayersAndPublish_observe_eq_selectionOnly
    (parameter : PublicParameter) (table : OtsSecretIndex → HashOutput)
    (ftsSecret : Index → FtsTree → FtsLeaf → Digest)
    (randomness : Randomness) (index : Index) (leaves : DigestTree → FtsLeaf)
    (ftsPath : FtsTree → Fin ftsTreeHeight → Digest)
    (context : DeferredContext) (fuel : Nat) (cache : SplitHashCache)
    {observe : DeferredContext → Nat →
      (Option Signature × SplitHashCache) → ProbComp Bool}
    [ObserverDooms table observe] [ObserverSynchronized table observe]
    [ObserverPositionNeutral table observe]
    (hvalid : context.Valid) (hcompletable : DeferredCompletable table context) :
    evalDist (runDeferredChronologicalLayersAndPublish parameter table ftsSecret randomness
        index leaves ftsPath context fuel cache >>= finishObserve observe) =
      evalDist (runSelectionOnlyLayersAndPublish parameter table ftsSecret randomness index
        leaves ftsPath context fuel cache >>= finishObserve observe) := by
  calc
    _ = evalDist (runDeferredLayersAndPublish parameter table ftsSecret randomness index leaves
          ftsPath deferredLayerSchedule context fuel cache >>= finishObserve observe) :=
      evalDist_runDeferredChronologicalLayersAndPublish_observe_eq_deferred parameter table
        ftsSecret randomness index leaves ftsPath context fuel cache observe
    _ = _ := evalDist_runDeferredLayersAndPublish_observe_eq_selectionOnly parameter table
      ftsSecret randomness index leaves ftsPath context fuel cache hvalid hcompletable

set_option maxRecDepth 100000 in
theorem evalDist_runDeferredChronologicalSignAfterDigest_observe_eq_selectionOnly
    (parameter : PublicParameter) (table : OtsSecretIndex → HashOutput)
    (ftsSecret : Index → FtsTree → FtsLeaf → Digest)
    (randomness : Randomness) (index : Index) (leaves : DigestTree → FtsLeaf)
    (context : DeferredContext) (fuel : Nat) (cache : SplitHashCache)
    {observe : DeferredContext → Nat →
      (Option Signature × SplitHashCache) → ProbComp Bool}
    [ObserverDooms table observe] [ObserverSynchronized table observe]
    [ObserverPositionNeutral table observe]
    (hvalid : context.Valid) (hcompletable : DeferredCompletable table context) :
    evalDist (runDeferredChronologicalSignAfterDigest parameter table ftsSecret randomness
        index leaves context fuel cache >>= finishObserve observe) =
      evalDist (runSelectionOnlySignAfterDigest parameter table ftsSecret randomness index
        leaves context fuel cache >>= finishObserve observe) := by
  unfold runDeferredChronologicalSignAfterDigest runSelectionOnlySignAfterDigest
  simp only [bind_assoc]
  apply evalDist_bind_congr
  intro ftsOption hfts
  cases ftsOption with
  | none => simp [finishObserve]
  | some ftsResult =>
      have hftsInvariants :=
        valid_completable_of_mem_runResolvedFromTable_of_finalizationMaterializedCouples table
          (simulateQ ordinaryHashImpl (ftsOpen parameter index leaves (ftsSecret index)))
          (finalizationMaterializedCouples_simulateQ ordinaryHashImpl
            (finalizationMaterializedCouples_ordinaryHashImpl table)
            (ftsOpen parameter index leaves (ftsSecret index)))
          context fuel cache ftsResult hvalid hcompletable hfts
      exact evalDist_runDeferredChronologicalLayersAndPublish_observe_eq_selectionOnly parameter
        table ftsSecret randomness index leaves ftsResult.value.1 ftsResult.context
          ftsResult.remaining ftsResult.value.2 hftsInvariants.1 hftsInvariants.2

set_option maxRecDepth 100000 in
theorem evalDist_runDeferredChronologicalSign_observe_eq_maskedSign
    (parameter : PublicParameter) (root : Digest)
    (table : OtsSecretIndex → HashOutput)
    (ftsSecret : Index → FtsTree → FtsLeaf → Digest) (message : Message)
    (context : DeferredContext) (fuel : Nat) (cache : SplitHashCache)
    {observe : DeferredContext → Nat →
      (Option Signature × SplitHashCache) → ProbComp Bool}
    [ObserverDooms table observe] [ObserverSynchronized table observe]
    [ObserverPositionNeutral table observe]
    (hvalid : context.Valid) (hcompletable : DeferredCompletable table context) :
    evalDist (runDeferredChronologicalSign parameter root table ftsSecret message context fuel
        cache >>= finishObserve observe) =
      evalDist (runResolvedObserve observe context fuel table
        ((maskedSign parameter root ftsSecret message).run cache)) := by
  calc
    _ = evalDist (runSelectionOnlySign parameter root table ftsSecret message context fuel cache >>=
          finishObserve observe) := by
      unfold runDeferredChronologicalSign runSelectionOnlySign
      simp only [bind_assoc]
      apply evalDist_bind_congr
      intro selectedOption hselected
      cases selectedOption with
      | none => simp [finishObserve]
      | some selected =>
          cases hvalue : selected.value.1 with
          | none => simp [hvalue, finishObserve]
          | some digestResult =>
              rcases digestResult with ⟨randomness, selectedIndex, leaves⟩
              simp only [hvalue]
              let secretKey : SecretKey :=
                ⟨parameter, root, fun _ _ _ _ => 0, ftsSecret⟩
              have hselectedInvariants :=
                valid_completable_of_mem_runResolvedFromTable_of_finalizationMaterializedCouples
                  table
                  (simulateQ ordinaryRomImpl
                    (signDigestLoop digestAttemptLimit secretKey message))
                  (finalizationMaterializedCouples_simulateQ ordinaryRomImpl
                    (finalizationMaterializedCouples_ordinaryRomImpl table)
                    (signDigestLoop digestAttemptLimit secretKey message))
                  context fuel cache selected hvalid hcompletable (by
                    simpa only [secretKey] using hselected)
              exact
                evalDist_runDeferredChronologicalSignAfterDigest_observe_eq_selectionOnly
                  parameter table ftsSecret randomness selectedIndex leaves selected.context
                    selected.remaining selected.value.2 hselectedInvariants.1
                      hselectedInvariants.2
    _ = evalDist (runResolvedFromTable context fuel table
          ((maskedSign parameter root ftsSecret message).run cache) >>= finishObserve observe) := by
      rw [evalDist_bind, evalDist_bind,
        evalDist_runSelectionOnlySign_eq_resolved parameter root table ftsSecret message context
          fuel cache hvalid.valuesConsistent
            (startTableAgrees_of_deferredCompletable hcompletable)]
    _ = _ := rfl

noncomputable def canonicalizeObserve
    (table : OtsSecretIndex → HashOutput)
    (observe : DeferredContext → Nat → α → ProbComp Bool)
    (context : DeferredContext) (fuel : Nat) (value : α) : ProbComp Bool := by
  classical
  exact if PublishedValues context.state then
      observe (canonicalizeMaterializedValues table context) fuel value
    else
      pure true

instance canonicalizeObserve_observerDooms
    (table : OtsSecretIndex → HashOutput)
    (observe : DeferredContext → Nat → α → ProbComp Bool)
    [ObserverDooms table observe] :
    ObserverDooms table (canonicalizeObserve table observe) where
  eq_true context fuel value hconsistent hstarts hdoomed := by
    unfold canonicalizeObserve
    split
    next _ =>
      exact ObserverDooms.eq_true
        (table := table) (observe := observe)
        (canonicalizeMaterializedValues table context) fuel value
        (canonicalizeMaterializedValues_valuesConsistent table context hconsistent)
        (canonicalizeMaterializedValues_startTableAgrees table context)
        (doomedResolvedContext_canonicalizeMaterializedValues
          (table := table) ⟨hconsistent, hstarts, hdoomed⟩).2.2
    next _ => rfl

instance canonicalizeObserve_observerSynchronized
    (table : OtsSecretIndex → HashOutput)
    (observe : DeferredContext → Nat → α → ProbComp Bool)
    [ObserverSynchronized table observe] :
    ObserverSynchronized table (canonicalizeObserve table observe) where
  eq_of_synchronized left right fuel value hcontext hvalues hrevealed := by
    have hpublishedIff : PublishedValues left.state ↔ PublishedValues right.state := by
      simp only [PublishedValues]
      constructor
      · intro hpublished coordinate hrightRevealed
        rw [← hvalues]
        exact hpublished coordinate (by simpa [hrevealed] using hrightRevealed)
      · intro hpublished coordinate hleftRevealed
        rw [hvalues]
        exact hpublished coordinate (by simpa [hrevealed] using hleftRevealed)
    unfold canonicalizeObserve
    split
    next hleftPublished =>
      have hrightPublished := hpublishedIff.mp hleftPublished
      simp only [hrightPublished, ↓reduceIte]
      have hcanonical := canonicalizedFinalizationContextEq hcontext hrevealed
      exact ObserverSynchronized.eq_of_synchronized
        (table := table) (observe := observe)
        (canonicalizeMaterializedValues table left)
        (canonicalizeMaterializedValues table right) fuel value
        hcanonical.1 hcanonical.2 hrevealed
    next hleftNotPublished =>
      have hrightNotPublished : ¬PublishedValues right.state := by
        rwa [← hpublishedIff]
      simp [hrightNotPublished]

set_option maxRecDepth 100000 in
theorem evalDist_resolveDeferredPositionValue_then_canonicalizeObserve
    (position : Position) (table : OtsSecretIndex → HashOutput)
    (observe : DeferredContext → Nat → α → ProbComp Bool)
    (hneutral : ObserverPositionNeutralAt table position observe)
    (context : DeferredContext) (fuel : Nat) (value : α)
    (hvalid : context.Valid) (hcompletable : DeferredCompletable table context)
    (hensured : Coordinate.position position ∈ context.state.ensured) :
    evalDist (resolveDeferredPositionValue position context >>= fun resolved =>
      match resolved with
      | none => pure true
      | some resolved =>
          canonicalizeObserve table observe resolved.toDeferredContext fuel value) =
      evalDist (canonicalizeObserve table observe context fuel value) := by
  by_cases hpublished : PublishedValues context.state
  · let finish : Option DeferredResolution → ProbComp Bool
      | none => pure true
      | some resolved => observe resolved.toDeferredContext fuel value
    have hclean : ∀ coordinate output,
        resolvedCompletionValue table context coordinate = some output →
          ¬context.state.hitAt coordinate output := by
      obtain ⟨completion, hcompletion⟩ := hcompletable
      intro coordinate output hvalue hhit
      have houtput := hcompletion.eq_resolvedCompletionValue coordinate output hvalue
      unfold LazyRevealProbe.State.hitAt at hhit
      rw [LazyRevealProbe.State.mem_pendingAt_iff] at hhit
      exact hcompletion.2.2.1 coordinate (truncateHash output) hhit (by rw [houtput])
    have hcanonicalValid :
        (canonicalizeMaterializedValues table context).Valid :=
      canonicalizeMaterializedValues_valid table context hvalid hclean
    have hcanonicalCompletable :
        DeferredCompletable table (canonicalizeMaterializedValues table context) := by
      obtain ⟨completion, hcompletion⟩ := hcompletable
      exact ⟨completion, hcompletion.to_canonicalizedMaterializedValues⟩
    have hcanonicalEnsured : Coordinate.position position ∈
        (canonicalizeMaterializedValues table context).state.ensured := hensured
    calc
      _ = evalDist (((Option.map (canonicalizeDeferredResolution table)) <$>
            resolveDeferredPositionValue position context) >>= finish) := by
          simp only [map_eq_bind_pure_comp, bind_assoc]
          apply evalDist_bind_congr
          intro resolved hresolved
          cases resolved with
          | none => rfl
          | some resolved =>
              have hresolvedPublished : PublishedValues resolved.state :=
                (publishedValues_resolveDeferredPositionValue_iff position context resolved
                  hresolved).2 hpublished
              simp [canonicalizeObserve, hresolvedPublished, finish,
                canonicalizeDeferredResolution]
      _ = evalDist (resolveDeferredPositionValue position
            (canonicalizeMaterializedValues table context) >>= finish) :=
          evalDist_bind_eq_of_evalDist_eq
            (evalDist_resolveDeferredPositionValue_canonicalize table position context
              hvalid.valuesConsistent hpublished)
            finish
      _ = evalDist (observe (canonicalizeMaterializedValues table context) fuel value) := by
          exact hneutral (canonicalizeMaterializedValues table context) fuel value
            hcanonicalValid hcanonicalCompletable hcanonicalEnsured
      _ = _ := by simp [canonicalizeObserve, hpublished]
  · calc
      _ = evalDist (resolveDeferredPositionValue position context >>= fun _ =>
            pure true) := by
          apply evalDist_bind_congr
          intro resolved hresolved
          cases resolved with
          | none => rfl
          | some resolved =>
              have hresolvedNotPublished : ¬PublishedValues resolved.state := by
                intro hresolvedPublished
                exact hpublished
                  ((publishedValues_resolveDeferredPositionValue_iff position context resolved
                    hresolved).1 hresolvedPublished)
              simp [canonicalizeObserve, hresolvedNotPublished]
      _ = evalDist (pure true : ProbComp Bool) :=
          OracleComp.DeferredSampling.evalDist_bind_const_neverFails
            (resolveDeferredPositionValue position context)
            (by simp [resolveDeferredPositionValue, LazyRevealProbe.sampleHashOutput])
            (pure true)
      _ = _ := by simp [canonicalizeObserve, hpublished]

instance canonicalizeObserve_observerPositionNeutral
    (table : OtsSecretIndex → HashOutput)
    (observe : DeferredContext → Nat → α → ProbComp Bool)
    [ObserverPositionNeutral table observe] :
    ObserverPositionNeutral table (canonicalizeObserve table observe) where
  eq_resolve position context fuel value hvalid hcompletable hensured :=
    evalDist_resolveDeferredPositionValue_then_canonicalizeObserve position table observe
      (ObserverPositionNeutral.at table position observe) context fuel value hvalid hcompletable
      hensured

theorem canonicalizeObserve_observerPositionNeutralAt
    (table : OtsSecretIndex → HashOutput) (position : Position)
    (observe : DeferredContext → Nat → α → ProbComp Bool)
    (hneutral : ObserverPositionNeutralAt table position observe) :
    ObserverPositionNeutralAt table position (canonicalizeObserve table observe) := by
  intro context fuel value hvalid hcompletable hensured
  exact evalDist_resolveDeferredPositionValue_then_canonicalizeObserve position table observe
    hneutral context fuel value hvalid hcompletable hensured

noncomputable def boundaryObserve
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
      runResolvedFromTable context fuel table ((impl query).run cache) >>=
        finishObserve (canonicalizeObserve table
          (fun nextContext remaining value =>
            recursivelyRun value.1 observe nextContext remaining table value.2)))
    computation observe context fuel table cache

set_option maxRecDepth 100000 in
theorem boundaryObserve_dooms
    (impl : QueryImpl spec
      (StateT SplitHashCache (OracleComp (LazyRevealProbe.World Coordinate))))
    (computation : OracleComp spec α)
    (observe : DeferredContext → Nat → (α × SplitHashCache) → ProbComp Bool)
    [ObserverDooms table observe]
    (context : DeferredContext) (fuel : Nat) (cache : SplitHashCache)
    (hconsistent : context.ValuesConsistent)
    (hstarts : StartTableAgrees context.state table)
    (hdoomed : ¬DeferredCompletable table context) :
    evalDist (boundaryObserve impl computation observe context fuel table cache) =
      evalDist (pure true : ProbComp Bool) := by
  induction computation using OracleComp.inductionOn generalizing context fuel cache with
  | pure value =>
      rw [boundaryObserve, OracleComp.construct_pure]
      exact ObserverDooms.eq_true context fuel (value, cache) hconsistent hstarts hdoomed
  | query_bind query next ih =>
      rw [boundaryObserve, OracleComp.construct_query_bind]
      let nextObserve : DeferredContext → Nat →
          ((spec.Range query) × SplitHashCache) → ProbComp Bool :=
        fun nextContext remaining value =>
          boundaryObserve impl (next value.1) observe nextContext remaining table value.2
      letI : ObserverDooms table nextObserve := ⟨by
        intro nextContext remaining value hnextConsistent hnextStarts hnextDoomed
        exact ih value.1 nextContext remaining value.2 hnextConsistent hnextStarts
          hnextDoomed⟩
      exact evalDist_runResolvedObserve_eq_true_of_not_completable_auto
        (observe := canonicalizeObserve table nextObserve)
        context fuel table ((impl query).run cache) hconsistent hstarts hdoomed

set_option maxRecDepth 100000 in
theorem boundaryObserve_synchronized
    (impl : QueryImpl spec
      (StateT SplitHashCache (OracleComp (LazyRevealProbe.World Coordinate))))
    (computation : OracleComp spec α)
    (observe : DeferredContext → Nat → (α × SplitHashCache) → ProbComp Bool)
    [ObserverDooms table observe] [ObserverSynchronized table observe]
    (left right : DeferredContext) (fuel : Nat)
    (cache : SplitHashCache)
    (hcontext : FinalizationContextEq table (some left) (some right))
    (hvalues : left.state.values = right.state.values)
    (hrevealed : left.state.revealed = right.state.revealed) :
    evalDist (boundaryObserve impl computation observe left fuel table cache) =
      evalDist (boundaryObserve impl computation observe right fuel table cache) := by
  induction computation using OracleComp.inductionOn generalizing left right fuel cache with
  | pure value =>
      rw [boundaryObserve, OracleComp.construct_pure,
        boundaryObserve, OracleComp.construct_pure]
      exact ObserverSynchronized.eq_of_synchronized left right fuel (value, cache)
        hcontext hvalues hrevealed
  | query_bind query next ih =>
      rw [boundaryObserve, OracleComp.construct_query_bind,
        boundaryObserve, OracleComp.construct_query_bind]
      let nextObserve : DeferredContext → Nat →
          ((spec.Range query) × SplitHashCache) → ProbComp Bool :=
        fun nextContext remaining value =>
          boundaryObserve impl (next value.1) observe nextContext remaining table value.2
      letI : ObserverDooms table nextObserve := ⟨by
        intro nextContext remaining value hnextConsistent hnextStarts hnextDoomed
        exact boundaryObserve_dooms impl (next value.1) observe nextContext remaining
          value.2 hnextConsistent hnextStarts hnextDoomed⟩
      letI : ObserverSynchronized table nextObserve := ⟨by
        intro nextLeft nextRight remaining value hnextContext hnextValues hnextRevealed
        exact ih value.1 nextLeft nextRight remaining value.2 hnextContext hnextValues
          hnextRevealed⟩
      letI : ObserverDooms table (canonicalizeObserve table nextObserve) := inferInstance
      letI : ObserverSynchronized table
          (canonicalizeObserve table nextObserve) := inferInstance
      exact evalDist_runResolvedObserve_eq_of_finalizationSynchronized
        (observe := canonicalizeObserve table nextObserve)
        ((impl query).run cache) left right fuel table hcontext hvalues hrevealed

set_option maxRecDepth 100000 in
theorem boundaryObserve_positionNeutral
    (impl : QueryImpl spec
      (StateT SplitHashCache (OracleComp (LazyRevealProbe.World Coordinate))))
    (computation : OracleComp spec α)
    (observe : DeferredContext → Nat → (α × SplitHashCache) → ProbComp Bool)
    [ObserverDooms table observe] [ObserverPositionNeutral table observe]
    (position : Position) (context : DeferredContext) (fuel : Nat)
    (cache : SplitHashCache) (hvalid : context.Valid)
    (hcompletable : DeferredCompletable table context)
    (hensured : Coordinate.position position ∈ context.state.ensured) :
    evalDist (resolveDeferredPositionValue position context >>= fun resolved =>
      match resolved with
      | none => pure true
      | some resolved =>
          boundaryObserve impl computation observe resolved.toDeferredContext fuel table
            cache) =
      evalDist (boundaryObserve impl computation observe context fuel table cache) := by
  induction computation using OracleComp.inductionOn generalizing position context fuel cache with
  | pure value =>
      rw [boundaryObserve, OracleComp.construct_pure]
      exact ObserverPositionNeutral.eq_resolve
        (table := table) (observe := observe) position context fuel (value, cache)
          hvalid hcompletable hensured
  | query_bind query next ih =>
      rw [boundaryObserve, OracleComp.construct_query_bind]
      let nextObserve : DeferredContext → Nat →
          ((spec.Range query) × SplitHashCache) → ProbComp Bool :=
        fun nextContext remaining value =>
          boundaryObserve impl (next value.1) observe nextContext remaining table value.2
      letI : ObserverDooms table nextObserve := ⟨by
        intro nextContext remaining value hnextConsistent hnextStarts hnextDoomed
        exact boundaryObserve_dooms impl (next value.1) observe nextContext remaining
          value.2 hnextConsistent hnextStarts hnextDoomed⟩
      letI : ObserverPositionNeutral table nextObserve := ⟨by
        intro nextPosition nextContext remaining value hnextValid hnextCompletable hnextEnsured
        exact ih value.1 nextPosition nextContext remaining value.2 hnextValid
          hnextCompletable hnextEnsured⟩
      letI : ObserverDooms table (canonicalizeObserve table nextObserve) := inferInstance
      letI : ObserverPositionNeutral table
          (canonicalizeObserve table nextObserve) := inferInstance
      exact evalDist_resolveDeferredPositionValue_then_runResolvedObserve_auto position
        (observe := canonicalizeObserve table nextObserve)
        ((impl query).run cache) context fuel table hvalid hcompletable hensured

set_option maxRecDepth 100000 in
theorem evalDist_canonicalDeferredAdversaryImpl_observe
    (parameter : PublicParameter) (root : Digest)
    (table : OtsSecretIndex → HashOutput)
    (ftsSecret : Index → FtsTree → FtsLeaf → Digest)
    (query : (OracleWorld + SigningSpec).Domain)
    (observe : DeferredContext → Nat →
      ((OracleWorld + SigningSpec).Range query × SplitHashCache) → ProbComp Bool)
    [ObserverDooms table observe] [ObserverSynchronized table observe]
    [ObserverPositionNeutral table observe]
    (context : DeferredContext) (fuel : Nat) (cache : SplitHashCache)
    (hvalid : context.Valid) (hcompletable : DeferredCompletable table context)
    (hpublished : PublishedValues context.state) :
    evalDist
        (canonicalDeferredAdversaryImpl parameter root table ftsSecret query context fuel table
          cache >>= finishObserve observe) =
      evalDist (runResolvedObserve (canonicalizeObserve table observe) context fuel table
        ((maskedExpandedAdversaryImpl parameter root ftsSecret query).run cache)) := by
  letI : ObserverDooms table (canonicalizeObserve table observe) := inferInstance
  letI : ObserverSynchronized table (canonicalizeObserve table observe) := inferInstance
  letI : ObserverPositionNeutral table
      (canonicalizeObserve table observe) := inferInstance
  cases query with
  | inl oracleQuery =>
      rw [canonicalDeferredAdversaryImpl]
      simp only [bind_assoc, pure_bind]
      unfold runResolvedObserve
      apply evalDist_bind_congr
      intro rawOption hraw
      cases rawOption with
      | none => simp [canonicalizeResolvedRun, finishObserve]
      | some rawResult =>
          have hrawPublished :=
            resolvedPreservesPublishedValuesImpl_probingRomImpl parameter oracleQuery context
              cache fuel table rawResult hpublished hraw
          simp [canonicalizeResolvedRun, finishObserve, canonicalizeObserve,
            hrawPublished]
  | inr message =>
      let hdooms : ObserverDooms table (canonicalizeObserve table observe) :=
        canonicalizeObserve_observerDooms table observe
      let hsync : ObserverSynchronized table (canonicalizeObserve table observe) :=
        canonicalizeObserve_observerSynchronized table observe
      let hposition : ObserverPositionNeutral table
          (canonicalizeObserve table observe) :=
        canonicalizeObserve_observerPositionNeutral table observe
      letI := hdooms
      letI := hsync
      letI := hposition
      rw [canonicalDeferredAdversaryImpl]
      simp only [bind_assoc, pure_bind]
      calc
        _ = evalDist (runDeferredChronologicalSign parameter root table ftsSecret message context
              fuel cache >>= finishObserve (canonicalizeObserve table observe)) := by
            apply evalDist_bind_congr
            intro rawOption hraw
            cases rawOption with
            | none => simp [canonicalizeResolvedRun, finishObserve]
            | some rawResult =>
                have hrawPublished := publishedValues_of_mem_runDeferredChronologicalSign
                  parameter root table ftsSecret message context fuel cache rawResult hpublished
                    hraw
                simp [canonicalizeResolvedRun, finishObserve, canonicalizeObserve,
                  hrawPublished]
        _ = _ := @evalDist_runDeferredChronologicalSign_observe_eq_maskedSign
          parameter root table ftsSecret message context fuel cache
            (canonicalizeObserve table observe) hdooms hsync hposition hvalid hcompletable

theorem valid_of_resolvedCore_completable
    (table : OtsSecretIndex → HashOutput) (context : DeferredContext)
    (hconsistent : context.ValuesConsistent)
    (hstarts : StartTableAgrees context.state table)
    (hcompletable : DeferredCompletable table context) : context.Valid := by
  refine ⟨hconsistent, ?_⟩
  intro coordinate output hvalue hhit
  obtain ⟨completion, hcompletion⟩ := hcompletable
  have hresolved : resolvedCompletionValue table context coordinate = some output := by
    cases coordinate with
    | chainStart lay tree leafIdx chainIdx =>
        simpa [resolvedCompletionValue] using
          (hstarts ⟨lay, tree, leafIdx, chainIdx⟩ output hvalue).symm
    | position position =>
        simp [resolvedCompletionValue, DeferredContext.positionValue, hvalue]
  have houtput := hcompletion.eq_resolvedCompletionValue coordinate output hresolved
  unfold LazyRevealProbe.State.hitAt at hhit
  rw [LazyRevealProbe.State.mem_pendingAt_iff] at hhit
  exact hcompletion.2.2.1 coordinate (truncateHash output) hhit (by rw [houtput])

set_option maxRecDepth 100000 in
theorem canonicalDeferredAdversaryImpl_core
    (parameter : PublicParameter) (root : Digest)
    (table : OtsSecretIndex → HashOutput)
    (ftsSecret : Index → FtsTree → FtsLeaf → Digest)
    (query : (OracleWorld + SigningSpec).Domain)
    (context : DeferredContext) (fuel : Nat) (cache : SplitHashCache)
    (result : ResolvedRunResult
      ((OracleWorld + SigningSpec).Range query × SplitHashCache))
    (hvalid : context.Valid) (hcompletable : DeferredCompletable table context)
    (hpublished : PublishedValues context.state)
    (hresult : some result ∈ support
      (canonicalDeferredAdversaryImpl parameter root table ftsSecret query context fuel table
        cache)) :
    result.table = table ∧ result.context.ValuesConsistent ∧
      StartTableAgrees result.context.state table ∧ PublishedValues result.context.state := by
  have hstarts := startTableAgrees_of_deferredCompletable hcompletable
  cases query with
  | inl oracleQuery =>
      rw [canonicalDeferredAdversaryImpl, mem_support_bind_iff] at hresult
      obtain ⟨rawOption, hraw, hcanonical⟩ := hresult
      cases rawOption with
      | none =>
          have hfalse : some result = none := by
            simpa only [canonicalizeResolvedRun, support_pure, Set.mem_singleton_iff] using
              hcanonical
          contradiction
      | some rawResult =>
          simp only [canonicalizeResolvedRun, mem_support_pure_iff] at hcanonical
          have hresultEq : result =
              { rawResult with
                context := canonicalizeMaterializedValues table rawResult.context } :=
            Option.some.inj hcanonical
          subst result
          have hcore := resolvedCore_of_mem_runResolvedFromTable
            ((probingRomImpl parameter oracleQuery).run cache) context fuel table rawResult
              hvalid.valuesConsistent hstarts hraw
          have hrawPublished :=
            resolvedPreservesPublishedValuesImpl_probingRomImpl parameter oracleQuery context
              cache fuel table rawResult hpublished hraw
          exact ⟨hcore.1,
            canonicalizeMaterializedValues_valuesConsistent table rawResult.context hcore.2.1,
            canonicalizeMaterializedValues_startTableAgrees table rawResult.context,
            hrawPublished.to_canonicalizedMaterializedValues⟩
  | inr message =>
      rw [canonicalDeferredAdversaryImpl, mem_support_bind_iff] at hresult
      obtain ⟨rawOption, hraw, hcanonical⟩ := hresult
      cases rawOption with
      | none =>
          have hfalse : some result = none := by
            simpa only [canonicalizeResolvedRun, support_pure, Set.mem_singleton_iff] using
              hcanonical
          contradiction
      | some rawResult =>
          simp only [canonicalizeResolvedRun, mem_support_pure_iff] at hcanonical
          have hresultEq : result =
              { rawResult with
                context := canonicalizeMaterializedValues table rawResult.context } :=
            Option.some.inj hcanonical
          subst result
          have hrawValid := valid_of_mem_runDeferredChronologicalSign parameter root table
            ftsSecret message context fuel cache rawResult hvalid hcompletable hraw
          have hrawPublished := publishedValues_of_mem_runDeferredChronologicalSign parameter root
            table ftsSecret message context fuel cache rawResult hpublished hraw
          have hview := finalizationViewEq_of_deferredCompletion_iff hvalid hvalid hstarts hstarts
            rfl hcompletable (fun _ => Iff.rfl)
          have hrelation :=
            relTriple_runResolvedFromTable_maskedPublishedChronologicalSign_finalization parameter
              root table ftsSecret message context context fuel cache cache
                ⟨hview, hvalid, hvalid, hcompletable⟩ rfl rfl
          obtain ⟨leftOption, _hleft, hrelated⟩ :=
            exists_right_of_relTriple_of_mem_support
              (OracleComp.ProgramLogic.Relational.relTriple_symm hrelation) hraw
          cases leftOption with
          | none => simp [FinalizationMaterializedRunEq] at hrelated
          | some leftResult =>
            simp only [FinalizationMaterializedRunEq] at hrelated
            rcases hrelated with
              ⟨_houtput, _hcontext, _hremaining, _hleftTable, hrawTable, _hcache,
                _hrevealed⟩
            exact ⟨hrawTable,
              canonicalizeMaterializedValues_valuesConsistent table rawResult.context
                hrawValid.valuesConsistent,
            canonicalizeMaterializedValues_startTableAgrees table rawResult.context,
              hrawPublished.to_canonicalizedMaterializedValues⟩

set_option maxRecDepth 100000 in
theorem evalDist_canonicalDeferred_adaptive_eq_boundaryObserve
    (parameter : PublicParameter) (root : Digest)
    (table : OtsSecretIndex → HashOutput)
    (ftsSecret : Index → FtsTree → FtsLeaf → Digest)
    (computation : OracleComp (OracleWorld + SigningSpec) α)
    (observe : DeferredContext → Nat → (α × SplitHashCache) → ProbComp Bool)
    [ObserverDooms table observe] [ObserverSynchronized table observe]
    [ObserverPositionNeutral table observe]
    (context : DeferredContext) (fuel : Nat) (cache : SplitHashCache)
    (hvalid : context.Valid) (hcompletable : DeferredCompletable table context)
    (hpublished : PublishedValues context.state) :
    evalDist
        (runSynchronizedResolved
          (canonicalDeferredAdversaryImpl parameter root table ftsSecret)
          computation context fuel table cache >>= finishObserve observe) =
      evalDist
        (boundaryObserve (maskedExpandedAdversaryImpl parameter root ftsSecret)
          computation observe context fuel table cache) := by
  induction computation using OracleComp.inductionOn generalizing context fuel cache with
  | pure value =>
      rw [runSynchronizedResolved_pure _ value context fuel table cache hcompletable,
        boundaryObserve, OracleComp.construct_pure]
      simp [finishObserve]
  | query_bind query next ih =>
      rw [runSynchronizedResolved, OracleComp.construct_query_bind,
        boundaryObserve, OracleComp.construct_query_bind]
      simp only [dif_pos hcompletable, bind_assoc]
      let nextObserve : DeferredContext → Nat →
          ((OracleWorld + SigningSpec).Range query × SplitHashCache) → ProbComp Bool :=
        fun nextContext remaining value =>
          boundaryObserve (maskedExpandedAdversaryImpl parameter root ftsSecret)
            (next value.1) observe nextContext remaining table value.2
      letI : ObserverDooms table nextObserve := ⟨by
        intro nextContext remaining value hnextConsistent hnextStarts hnextDoomed
        exact boundaryObserve_dooms
          (maskedExpandedAdversaryImpl parameter root ftsSecret) (next value.1) observe
            nextContext remaining value.2 hnextConsistent hnextStarts hnextDoomed⟩
      letI : ObserverSynchronized table nextObserve := ⟨by
        intro nextLeft nextRight remaining value hnextContext hnextValues hnextRevealed
        exact boundaryObserve_synchronized
          (maskedExpandedAdversaryImpl parameter root ftsSecret) (next value.1) observe
            nextLeft nextRight remaining value.2 hnextContext hnextValues hnextRevealed⟩
      letI : ObserverPositionNeutral table nextObserve := ⟨by
        intro position nextContext remaining value hnextValid hnextCompletable hnextEnsured
        exact boundaryObserve_positionNeutral
          (maskedExpandedAdversaryImpl parameter root ftsSecret) (next value.1) observe position
            nextContext remaining value.2 hnextValid hnextCompletable hnextEnsured⟩
      calc
        _ = evalDist
            (canonicalDeferredAdversaryImpl parameter root table ftsSecret query context fuel
              table cache >>= finishObserve nextObserve) := by
              apply evalDist_bind_congr
              intro stepOption hstep
              cases stepOption with
              | none => simp [finishObserve]
              | some step =>
                  have hcore := canonicalDeferredAdversaryImpl_core parameter root table
                    ftsSecret query context fuel cache step hvalid hcompletable hpublished hstep
                  simp only [finishObserve]
                  rw [hcore.1]
                  change evalDist
                      (runSynchronizedResolved
                        (canonicalDeferredAdversaryImpl parameter root table ftsSecret)
                        (next step.value.1) step.context step.remaining table
                          step.value.2 >>= finishObserve observe) =
                    evalDist
                      (boundaryObserve
                        (maskedExpandedAdversaryImpl parameter root ftsSecret)
                        (next step.value.1) observe step.context step.remaining table
                          step.value.2)
                  by_cases hnextCompletable : DeferredCompletable table step.context
                  · have hnextValid := valid_of_resolvedCore_completable table step.context
                      hcore.2.1 hcore.2.2.1 hnextCompletable
                    exact ih step.value.1 step.context step.remaining step.value.2 hnextValid
                      hnextCompletable hcore.2.2.2
                  · rw [runSynchronizedResolved_of_not_completable]
                    · exact (boundaryObserve_dooms
                        (maskedExpandedAdversaryImpl parameter root ftsSecret)
                          (next step.value.1) observe step.context step.remaining step.value.2
                            hcore.2.1 hcore.2.2.1 hnextCompletable).symm
                    · exact hnextCompletable
        _ = _ := evalDist_canonicalDeferredAdversaryImpl_observe parameter root table ftsSecret
          query nextObserve context fuel cache hvalid hcompletable hpublished

end SphincsSecurity.Concrete.OtsProbeSimulation
