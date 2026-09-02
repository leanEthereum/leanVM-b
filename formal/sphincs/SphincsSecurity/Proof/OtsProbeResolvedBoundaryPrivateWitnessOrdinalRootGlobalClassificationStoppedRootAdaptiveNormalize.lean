import SphincsSecurity.Proof.OtsProbeResolvedBoundaryPrivateWitnessOrdinalRootGlobalClassificationStoppedRootAdaptiveTrace
import SphincsSecurity.Proof.OtsProbeResolvedPrivateRetainedCommutation

/-!
# Adaptive selected-root normalization

The selected-root computation resolves its target only when the chosen candidate is reached. This
module moves that same resolution to the start of the deferred prefix. The post-selection suffix is
already handled by the adaptive selected-root bridge, so the normalization stops at that boundary.
-/

namespace SphincsSecurity.Concrete.OtsProbeSimulation

open OracleComp OracleSpec
open OracleComp.ProgramLogic.Relational

noncomputable def eagerDirectDelayedSelectedRootIndicator
    (ordinal : Nat) (parameter : PublicParameter) (root : Digest)
    (ftsSecret : Index → FtsTree → FtsLeaf → Digest)
    (table : OtsSecretIndex → HashOutput) (target : Position) (rightRoot : Digest)
    (computation : OracleComp (OracleWorld + SigningSpec) α)
    (snapshots : List PlannedProbeSnapshot)
    (observations : List CleanProbeObservation)
    (context : DeferredContext) (fuel : Nat) (cache : SplitHashCache) : ProbComp Bool :=
  if ordinal < snapshots.length then
    directDelayedSelectedRootIndicator ordinal parameter root ftsSecret table target rightRoot
      computation snapshots observations context fuel cache
  else do
    let resolved ← resolveDeferredPositionValue target context
    match resolved with
    | none => pure false
    | some resolved =>
        directDelayedSelectedRootIndicator ordinal parameter root ftsSecret table target rightRoot
          computation snapshots observations resolved.toDeferredContext fuel cache

set_option maxRecDepth 100000 in
theorem evalDist_eagerDirectDelayedSelectedRootIndicator_eq_of_selected
    (ordinal : Nat) (parameter : PublicParameter) (root : Digest)
    (ftsSecret : Index → FtsTree → FtsLeaf → Digest)
    (table : OtsSecretIndex → HashOutput) (target : Position) (rightRoot : Digest)
    (computation : OracleComp (OracleWorld + SigningSpec) α)
    (snapshots : List PlannedProbeSnapshot)
    (observations : List CleanProbeObservation)
    (context : DeferredContext) (fuel : Nat) (cache : SplitHashCache)
    (hselected : ordinal < snapshots.length) :
    evalDist
        (eagerDirectDelayedSelectedRootIndicator ordinal parameter root ftsSecret table target
          rightRoot computation snapshots observations context fuel cache) =
      evalDist
        (directDelayedSelectedRootIndicator ordinal parameter root ftsSecret table target
          rightRoot computation snapshots observations context fuel cache) := by
  simp [eagerDirectDelayedSelectedRootIndicator, hselected]

theorem evalDist_eagerDirectDelayedSelectedRootIndicator_pure_eq
    (ordinal : Nat) (parameter : PublicParameter) (root : Digest)
    (ftsSecret : Index → FtsTree → FtsLeaf → Digest)
    (table : OtsSecretIndex → HashOutput) (target : Position) (rightRoot : Digest)
    (value : α) (snapshots : List PlannedProbeSnapshot)
    (observations : List CleanProbeObservation)
    (context : DeferredContext) (fuel : Nat) (cache : SplitHashCache)
    (hselected : ¬ordinal < snapshots.length) :
    evalDist
        (eagerDirectDelayedSelectedRootIndicator ordinal parameter root ftsSecret table target
          rightRoot (pure value) snapshots observations context fuel cache) =
      evalDist
        (directDelayedSelectedRootIndicator ordinal parameter root ftsSecret table target
          rightRoot (pure value) snapshots observations context fuel cache) := by
  simp only [eagerDirectDelayedSelectedRootIndicator, hselected, ↓reduceIte,
    directDelayedSelectedRootIndicator, OracleComp.construct_pure, ↓reduceDIte]
  calc
    _ = evalDist
        (resolveDeferredPositionValue target context >>= fun _ ↦
          (pure false : ProbComp Bool)) := by
      apply evalDist_bind_congr
      intro resolved _hresolved
      cases resolved <;> rfl
    _ = evalDist (pure false : ProbComp Bool) :=
      OracleComp.DeferredSampling.evalDist_bind_const_neverFails
        (resolveDeferredPositionValue target context)
        (by simp [resolveDeferredPositionValue, LazyRevealProbe.sampleHashOutput])
        (pure false)

theorem evalDist_eagerDirectDelayedSelectedRootIndicator_of_resolved
    (ordinal : Nat) (parameter : PublicParameter) (root : Digest)
    (ftsSecret : Index → FtsTree → FtsLeaf → Digest)
    (table : OtsSecretIndex → HashOutput) (target : Position) (rightRoot : Digest)
    (computation : OracleComp (OracleWorld + SigningSpec) α)
    (snapshots : List PlannedProbeSnapshot)
    (observations : List CleanProbeObservation)
    (context : DeferredContext) (resolved : DeferredResolution)
    (fuel : Nat) (cache : SplitHashCache)
    (hresolved : some resolved ∈ support
      (resolveDeferredPositionValue target context)) :
    evalDist
        (eagerDirectDelayedSelectedRootIndicator ordinal parameter root ftsSecret table target
          rightRoot computation snapshots observations resolved.toDeferredContext fuel cache) =
      evalDist
        (directDelayedSelectedRootIndicator ordinal parameter root ftsSecret table target
          rightRoot computation snapshots observations resolved.toDeferredContext fuel cache) := by
  by_cases hselected : ordinal < snapshots.length
  · exact evalDist_eagerDirectDelayedSelectedRootIndicator_eq_of_selected ordinal parameter
      root ftsSecret table target rightRoot computation snapshots observations
      resolved.toDeferredContext fuel cache hselected
  · unfold eagerDirectDelayedSelectedRootIndicator
    simp only [hselected, ↓reduceIte]
    rw [resolveDeferredPositionValue_of_resolved target context resolved hresolved]
    rfl

set_option maxRecDepth 100000 in
theorem evalDist_resolveDeferredPositionValue_then_canonicalizeDirectDelayed
    (table : OtsSecretIndex → HashOutput) (target : Position)
    (observe : DeferredContext → Nat → α → List PlannedProbeSnapshot →
      List CleanProbeObservation → ProbComp Bool)
    (context : DeferredContext) (fuel : Nat) (value : α)
    (snapshots : List PlannedProbeSnapshot)
    (observations : List CleanProbeObservation)
    (hvalid : context.Valid) (hcompletable : DeferredCompletable table context)
    (hpublished : PublishedValues context.state)
    (hnormalize : evalDist (resolveDeferredPositionValue target
          (canonicalizeMaterializedValues table context) >>= fun resolved ↦
        match resolved with
        | none => pure false
        | some resolved =>
            observe resolved.toDeferredContext fuel value snapshots observations) =
      evalDist (observe (canonicalizeMaterializedValues table context) fuel value snapshots
        observations)) :
    evalDist (resolveDeferredPositionValue target context >>= fun resolved ↦
        match resolved with
        | none => pure false
        | some resolved =>
            canonicalizeDirectDelayedSelectedRootIndicator table observe
              resolved.toDeferredContext fuel value snapshots observations) =
      evalDist (canonicalizeDirectDelayedSelectedRootIndicator table observe context fuel value
        snapshots observations) := by
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
      DeferredCompletable table (canonicalizeMaterializedValues table context) :=
    (valid_completable_canonicalizeMaterializedValues table context hvalid hcompletable).2
  have hcanonicalNoHit :
      ¬PrivateStructuralHit (canonicalizeMaterializedValues table context) :=
    not_privateStructuralHit_of_deferredCompletable hcanonicalCompletable
  have hright : evalDist
      (canonicalizeDirectDelayedSelectedRootIndicator table observe context fuel value snapshots
        observations) =
      evalDist (observe (canonicalizeMaterializedValues table context) fuel value snapshots
        observations) := by
    simp [canonicalizeDirectDelayedSelectedRootIndicator, hcanonicalNoHit, hpublished,
      hcanonicalCompletable]
  rw [hright]
  let finish : Option DeferredResolution → ProbComp Bool
    | none => pure false
    | some resolved => observe resolved.toDeferredContext fuel value snapshots observations
  calc
    _ = evalDist (((Option.map (canonicalizeDeferredResolution table)) <$>
          resolveDeferredPositionValue target context) >>= finish) := by
      simp only [map_eq_bind_pure_comp, bind_assoc]
      apply evalDist_bind_congr
      intro resolved hresolved
      cases resolved with
      | none => rfl
      | some resolved =>
          have hresolvedValid := hvalid.of_resolveDeferredPositionValue target resolved hresolved
          have hresolvedCompletable :=
            hcompletable.of_resolveDeferredPositionValue hvalid target resolved hresolved
          have hresolvedPublished : PublishedValues resolved.state :=
            (publishedValues_resolveDeferredPositionValue_iff target context resolved
              hresolved).2 hpublished
          have hcanonical := valid_completable_canonicalizeMaterializedValues table
            resolved.toDeferredContext hresolvedValid hresolvedCompletable
          have hcanonicalNoHit : ¬PrivateStructuralHit
              (canonicalizeMaterializedValues table resolved.toDeferredContext) :=
            not_privateStructuralHit_of_deferredCompletable hcanonical.2
          simp [canonicalizeDirectDelayedSelectedRootIndicator, hcanonicalNoHit,
            hresolvedPublished, hcanonical.2, finish, canonicalizeDeferredResolution]
    _ = evalDist (resolveDeferredPositionValue target
          (canonicalizeMaterializedValues table context) >>= finish) :=
      evalDist_bind_eq_of_evalDist_eq
        (evalDist_resolveDeferredPositionValue_canonicalize table target context
          hvalid.valuesConsistent hpublished) finish
    _ = _ := hnormalize

theorem runDirectResolvedWitnessFromTable_splitUniformImpl
    (n fuel : Nat) (context : DeferredContext)
    (table : OtsSecretIndex → HashOutput) (cache : SplitHashCache) :
    runDirectResolvedWitnessFromTable context fuel table ((splitUniformImpl n).run cache) = (do
      let output ← liftM (unifSpec.query n)
      pure (DirectWitnessResult.done ⟨context, fuel, (output, cache), table⟩)) := by
  rfl

noncomputable def negatedDirectDelayedObserve
    (observe : DeferredContext → Nat → α → List PlannedProbeSnapshot →
      List CleanProbeObservation → ProbComp Bool)
    (snapshots : List PlannedProbeSnapshot)
    (observations : List CleanProbeObservation)
    (context : DeferredContext) (fuel : Nat) (value : α) : ProbComp Bool :=
  Bool.not <$> observe context fuel value snapshots observations

set_option maxRecDepth 100000 in
theorem evalDist_runDirectWitness_finish_false_eq_complement_runDirectObserve
    (observe : DeferredContext → Nat → α → List PlannedProbeSnapshot →
      List CleanProbeObservation → ProbComp Bool)
    (snapshots : List PlannedProbeSnapshot)
    (observations : List CleanProbeObservation)
    (context : DeferredContext) (fuel : Nat)
    (table : OtsSecretIndex → HashOutput)
    (computation : OracleComp (LazyRevealProbe.World Coordinate) α) :
    evalDist (runDirectResolvedWitnessFromTable context fuel table computation >>=
        finishDirectDelayedSelectedRootIndicator observe snapshots observations) =
      evalDist (Bool.not <$> runDirectResolvedObserve
        (negatedDirectDelayedObserve observe snapshots observations)
        context fuel table computation) := by
  unfold runDirectResolvedObserve
  rw [← map_toOption_runDirectResolvedDetailedFromTable computation context fuel table]
  rw [← map_erase_runDirectResolvedWitnessFromTable computation context fuel table]
  simp only [map_eq_bind_pure_comp, bind_assoc]
  apply evalDist_bind_congr
  intro result _hresult
  cases result <;>
    simp [finishDirectDelayedSelectedRootIndicator, finishObserve,
      DirectWitnessResult.erase, DirectDetailedResult.toOption, negatedDirectDelayedObserve]

set_option maxRecDepth 100000 in
theorem evalDist_complement_runDirectWitness_finish_false_eq_runDirectObserve
    (observe : DeferredContext → Nat → α → List PlannedProbeSnapshot →
      List CleanProbeObservation → ProbComp Bool)
    (snapshots : List PlannedProbeSnapshot)
    (observations : List CleanProbeObservation)
    (context : DeferredContext) (fuel : Nat)
    (table : OtsSecretIndex → HashOutput)
    (computation : OracleComp (LazyRevealProbe.World Coordinate) α) :
    evalDist (Bool.not <$> (runDirectResolvedWitnessFromTable context fuel table computation >>=
        finishDirectDelayedSelectedRootIndicator observe snapshots observations)) =
      evalDist (runDirectResolvedObserve
        (negatedDirectDelayedObserve observe snapshots observations)
        context fuel table computation) := by
  have hbridge := evalDist_runDirectWitness_finish_false_eq_complement_runDirectObserve observe
    snapshots observations context fuel table computation
  calc
    _ = evalDist (Bool.not <$> (Bool.not <$> runDirectResolvedObserve
          (negatedDirectDelayedObserve observe snapshots observations)
          context fuel table computation)) := by
            rw [evalDist_map, evalDist_map, hbridge]
    _ = _ := by simp

instance negatedCanonicalizeDirectDelayedObserve_observerDooms
    (table : OtsSecretIndex → HashOutput)
    (observe : DeferredContext → Nat → α → List PlannedProbeSnapshot →
      List CleanProbeObservation → ProbComp Bool)
    (snapshots : List PlannedProbeSnapshot)
    (observations : List CleanProbeObservation) :
    ObserverDooms table
      (negatedDirectDelayedObserve
        (canonicalizeDirectDelayedSelectedRootIndicator table observe)
        snapshots observations) where
  eq_true context fuel value hconsistent hstarts hdoomed := by
    have hcanonicalDoomed := doomedResolvedContext_canonicalizeMaterializedValues
      (table := table) (context := context) ⟨hconsistent, hstarts, hdoomed⟩
    unfold negatedDirectDelayedObserve canonicalizeDirectDelayedSelectedRootIndicator
    let canonical := canonicalizeMaterializedValues table context
    by_cases hhit : PrivateStructuralHit canonical
    · simp [canonical, hhit]
    · by_cases hpublished : PublishedValues context.state
      · simp [canonical, hhit, hpublished, hcanonicalDoomed.2.2]
      · simp [canonical, hhit, hpublished]

instance negatedCanonicalizeDirectDelayedObserve_observerSynchronized
    (table : OtsSecretIndex → HashOutput)
    (observe : DeferredContext → Nat → α → List PlannedProbeSnapshot →
      List CleanProbeObservation → ProbComp Bool)
    (snapshots : List PlannedProbeSnapshot)
    (observations : List CleanProbeObservation)
    [ObserverSynchronized table
      (negatedDirectDelayedObserve observe snapshots observations)] :
    ObserverSynchronized table
      (negatedDirectDelayedObserve
        (canonicalizeDirectDelayedSelectedRootIndicator table observe)
        snapshots observations) where
  eq_of_synchronized left right fuel value hcontext hvalues hrevealed := by
    rcases hcontext with ⟨hview, hleftValid, hrightValid, hleftCompletable⟩
    have hrightCompletable : DeferredCompletable table right := by
      rcases hleftCompletable with ⟨completion, hcompletion⟩
      exact ⟨completion, (hview.deferredCompletion_iff completion).mp hcompletion⟩
    have hleftCanonical := valid_completable_canonicalizeMaterializedValues table left
      hleftValid hleftCompletable
    have hrightCanonical := valid_completable_canonicalizeMaterializedValues table right
      hrightValid hrightCompletable
    have hleftNoHit :
        ¬PrivateStructuralHit (canonicalizeMaterializedValues table left) :=
      not_privateStructuralHit_of_deferredCompletable hleftCanonical.2
    have hrightNoHit :
        ¬PrivateStructuralHit (canonicalizeMaterializedValues table right) :=
      not_privateStructuralHit_of_deferredCompletable hrightCanonical.2
    have hpublishedIff : PublishedValues left.state ↔ PublishedValues right.state := by
      simp only [PublishedValues]
      constructor
      · intro hpublished coordinate hrightRevealed
        rw [← hvalues]
        exact hpublished coordinate (by simpa [hrevealed] using hrightRevealed)
      · intro hpublished coordinate hleftRevealed
        rw [hvalues]
        exact hpublished coordinate (by simpa [hrevealed] using hleftRevealed)
    unfold negatedDirectDelayedObserve canonicalizeDirectDelayedSelectedRootIndicator
    by_cases hleftPublished : PublishedValues left.state
    · have hrightPublished := hpublishedIff.mp hleftPublished
      simp only [hleftNoHit, hrightNoHit, hleftPublished, hrightPublished,
        hleftCanonical.2, hrightCanonical.2, ↓reduceIte]
      have hcanonical := canonicalizedFinalizationContextEq
        (⟨hview, hleftValid, hrightValid, hleftCompletable⟩ :
          FinalizationContextEq table (some left) (some right)) hrevealed
      exact ObserverSynchronized.eq_of_synchronized
        (table := table)
        (observe := negatedDirectDelayedObserve observe snapshots observations)
        (canonicalizeMaterializedValues table left)
        (canonicalizeMaterializedValues table right) fuel value hcanonical.1 hcanonical.2
        hrevealed
    · have hrightNotPublished : ¬PublishedValues right.state := by
        rwa [← hpublishedIff]
      simp [hleftNoHit, hrightNoHit, hleftPublished, hrightNotPublished]

theorem evalDist_negatedCanonicalizeDirectDelayedObserve_eq_canonicalizeObserve
    (table : OtsSecretIndex → HashOutput)
    (observe : DeferredContext → Nat → α → List PlannedProbeSnapshot →
      List CleanProbeObservation → ProbComp Bool)
    (snapshots : List PlannedProbeSnapshot)
    (observations : List CleanProbeObservation)
    (context : DeferredContext) (fuel : Nat) (value : α)
    (hvalid : context.Valid) (hcompletable : DeferredCompletable table context) :
    evalDist
        (negatedDirectDelayedObserve
          (canonicalizeDirectDelayedSelectedRootIndicator table observe)
          snapshots observations context fuel value) =
      evalDist
        (canonicalizeObserve table
          (negatedDirectDelayedObserve observe snapshots observations)
          context fuel value) := by
  have hcanonical := valid_completable_canonicalizeMaterializedValues table context hvalid
    hcompletable
  have hnoHit : ¬PrivateStructuralHit
      (canonicalizeMaterializedValues table context) :=
    not_privateStructuralHit_of_deferredCompletable hcanonical.2
  unfold negatedDirectDelayedObserve canonicalizeDirectDelayedSelectedRootIndicator
    canonicalizeObserve
  by_cases hpublished : PublishedValues context.state <;>
    simp [hnoHit, hpublished, hcanonical.2]

instance negatedCanonicalizeDirectDelayedObserve_observerPositionNeutral
    (table : OtsSecretIndex → HashOutput)
    (observe : DeferredContext → Nat → α → List PlannedProbeSnapshot →
      List CleanProbeObservation → ProbComp Bool)
    (snapshots : List PlannedProbeSnapshot)
    (observations : List CleanProbeObservation)
    [ObserverPositionNeutral table
      (negatedDirectDelayedObserve observe snapshots observations)] :
    ObserverPositionNeutral table
      (negatedDirectDelayedObserve
        (canonicalizeDirectDelayedSelectedRootIndicator table observe)
        snapshots observations) where
  eq_resolve position context fuel value hvalid hcompletable hensured := by
    let standard := canonicalizeObserve table
      (negatedDirectDelayedObserve observe snapshots observations)
    calc
      _ = evalDist (resolveDeferredPositionValue position context >>= fun resolved ↦
            match resolved with
            | none => pure true
            | some resolved => standard resolved.toDeferredContext fuel value) := by
          apply evalDist_bind_congr
          intro resolved hresolved
          cases resolved with
          | none => rfl
          | some resolved =>
              exact evalDist_negatedCanonicalizeDirectDelayedObserve_eq_canonicalizeObserve
                table observe snapshots observations resolved.toDeferredContext fuel value
                (hvalid.of_resolveDeferredPositionValue position resolved hresolved)
                (hcompletable.of_resolveDeferredPositionValue hvalid position resolved hresolved)
      _ = evalDist (standard context fuel value) :=
          ObserverPositionNeutral.eq_resolve
            (table := table)
            (observe := canonicalizeObserve table
              (negatedDirectDelayedObserve observe snapshots observations))
            position context fuel value hvalid hcompletable hensured
      _ = _ :=
          (evalDist_negatedCanonicalizeDirectDelayedObserve_eq_canonicalizeObserve table observe
            snapshots observations context fuel value hvalid hcompletable).symm

set_option maxRecDepth 100000 in
theorem evalDist_complement_runDirectWitness_finish_false_eq_of_synchronized
    (table : OtsSecretIndex → HashOutput)
    (observe : DeferredContext → Nat → α → List PlannedProbeSnapshot →
      List CleanProbeObservation → ProbComp Bool)
    (snapshots : List PlannedProbeSnapshot)
    (observations : List CleanProbeObservation)
    (computation : OracleComp (LazyRevealProbe.World Coordinate) α)
    (left right : DeferredContext) (fuel : Nat)
    (hcontext : FinalizationContextEq table (some left) (some right))
    (hvalues : left.state.values = right.state.values)
    (hrevealed : left.state.revealed = right.state.revealed)
    [ObserverSynchronized table
      (negatedDirectDelayedObserve observe snapshots observations)]
    [ObserverPositionNeutral table
      (negatedDirectDelayedObserve observe snapshots observations)] :
    evalDist (Bool.not <$>
        (runDirectResolvedWitnessFromTable left fuel table computation >>=
          finishDirectDelayedSelectedRootIndicator
            (canonicalizeDirectDelayedSelectedRootIndicator table observe)
            snapshots observations)) =
      evalDist (Bool.not <$>
        (runDirectResolvedWitnessFromTable right fuel table computation >>=
          finishDirectDelayedSelectedRootIndicator
            (canonicalizeDirectDelayedSelectedRootIndicator table observe)
            snapshots observations)) := by
  rcases hcontext with ⟨hview, hleftValid, hrightValid, hleftCompletable⟩
  have hrightCompletable : DeferredCompletable table right := by
    rcases hleftCompletable with ⟨completion, hcompletion⟩
    exact ⟨completion, (hview.deferredCompletion_iff completion).mp hcompletion⟩
  let nextObserve := negatedDirectDelayedObserve
    (canonicalizeDirectDelayedSelectedRootIndicator table observe) snapshots observations
  calc
    _ = evalDist (runDirectResolvedObserve nextObserve left fuel table computation) :=
      evalDist_complement_runDirectWitness_finish_false_eq_runDirectObserve
        (canonicalizeDirectDelayedSelectedRootIndicator table observe) snapshots observations
        left fuel table computation
    _ = evalDist (runResolvedObserve nextObserve left fuel table computation) :=
      (evalDist_runResolvedObserve_eq_runDirectResolvedObserve
        (observe := nextObserve) left fuel table computation hleftValid hleftCompletable).symm
    _ = evalDist (runResolvedObserve nextObserve right fuel table computation) :=
      evalDist_runResolvedObserve_eq_of_finalizationSynchronized computation left right fuel table
        ⟨hview, hleftValid, hrightValid, hleftCompletable⟩ hvalues hrevealed
    _ = evalDist (runDirectResolvedObserve nextObserve right fuel table computation) :=
      evalDist_runResolvedObserve_eq_runDirectResolvedObserve
        (observe := nextObserve) right fuel table computation hrightValid hrightCompletable
    _ = _ :=
      (evalDist_complement_runDirectWitness_finish_false_eq_runDirectObserve
        (canonicalizeDirectDelayedSelectedRootIndicator table observe) snapshots observations
        right fuel table computation).symm

theorem evalDist_eq_of_complement_eq
    (left right : ProbComp Bool)
    (hcomplement : evalDist (Bool.not <$> left) = evalDist (Bool.not <$> right)) :
    evalDist left = evalDist right := by
  have h := congrArg (Functor.map Bool.not) hcomplement
  simpa [evalDist_map, Functor.map_map] using h

set_option maxRecDepth 100000 in
theorem evalDist_resolve_then_runDirectWitness_finish_false
    (table : OtsSecretIndex → HashOutput) (target : Position)
    (observe : DeferredContext → Nat → α → List PlannedProbeSnapshot →
      List CleanProbeObservation → ProbComp Bool)
    (snapshots : List PlannedProbeSnapshot)
    (observations : List CleanProbeObservation)
    (computation : OracleComp (LazyRevealProbe.World Coordinate) α)
    (context : DeferredContext) (fuel : Nat)
    (hvalid : context.Valid) (hcompletable : DeferredCompletable table context)
    [ObserverSynchronized table
      (negatedDirectDelayedObserve observe snapshots observations)]
    [ObserverPositionNeutral table
      (negatedDirectDelayedObserve observe snapshots observations)] :
    evalDist (resolveDeferredPositionValue target context >>= fun resolved ↦
        match resolved with
        | none => pure false
        | some resolved =>
            runDirectResolvedWitnessFromTable resolved.toDeferredContext fuel table computation >>=
              finishDirectDelayedSelectedRootIndicator
                (canonicalizeDirectDelayedSelectedRootIndicator table observe)
                snapshots observations) =
      evalDist (runDirectResolvedWitnessFromTable context fuel table computation >>=
        finishDirectDelayedSelectedRootIndicator
          (canonicalizeDirectDelayedSelectedRootIndicator table observe)
          snapshots observations) := by
  let nextObserve := negatedDirectDelayedObserve
    (canonicalizeDirectDelayedSelectedRootIndicator table observe) snapshots observations
  apply evalDist_eq_of_complement_eq
  calc
    _ = evalDist (resolveDeferredPositionValue target context >>= fun resolved ↦
          match resolved with
          | none => pure true
          | some resolved =>
              runResolvedObserve nextObserve resolved.toDeferredContext fuel table computation) := by
        rw [map_bind]
        apply evalDist_bind_congr
        intro resolved hresolved
        cases resolved with
        | none => rfl
        | some resolved =>
            have hresolvedValid := hvalid.of_resolveDeferredPositionValue target resolved hresolved
            have hresolvedCompletable := hcompletable.of_resolveDeferredPositionValue hvalid target
              resolved hresolved
            calc
              _ = evalDist (runDirectResolvedObserve nextObserve resolved.toDeferredContext fuel
                    table computation) :=
                  evalDist_complement_runDirectWitness_finish_false_eq_runDirectObserve
                    (canonicalizeDirectDelayedSelectedRootIndicator table observe) snapshots
                    observations resolved.toDeferredContext fuel table computation
              _ = _ :=
                  (evalDist_runResolvedObserve_eq_runDirectResolvedObserve
                    (observe := nextObserve) resolved.toDeferredContext fuel table computation
                    hresolvedValid hresolvedCompletable).symm
    _ = evalDist (runResolvedObserve nextObserve context fuel table computation) :=
      evalDist_resolveDeferredPositionValue_then_runResolvedObserve_any
        (observe := nextObserve) target computation context fuel table hvalid hcompletable
    _ = evalDist (runDirectResolvedObserve nextObserve context fuel table computation) :=
      evalDist_runResolvedObserve_eq_runDirectResolvedObserve
        (observe := nextObserve) context fuel table computation hvalid hcompletable
    _ = _ :=
      (evalDist_complement_runDirectWitness_finish_false_eq_runDirectObserve
        (canonicalizeDirectDelayedSelectedRootIndicator table observe) snapshots observations
        context fuel table computation).symm

theorem cleanProbeObservation_materializedDeferredState_resolved
    (target : Position) (context : DeferredContext) (resolved : DeferredResolution)
    (hresolved : some resolved ∈ support
      (resolveDeferredPositionValue target context))
    (coordinate : Coordinate) (candidate : Digest) :
    cleanProbeObservation (materializedDeferredState resolved.toDeferredContext)
        coordinate candidate =
      installPositionValueAtProbe target resolved.output
        (cleanProbeObservation (materializedDeferredState context) coordinate candidate) := by
  have hstate := resolveDeferredPositionValue_state_eq_clearPending target context resolved
    hresolved
  have hstateValues := resolveDeferredPositionValue_preserves_state_values target context resolved
    hresolved
  cases coordinate with
  | chainStart lay tree leafIdx chainIdx =>
      simp [cleanProbeObservation, installPositionValueAtProbe, hstate,
        LazyRevealProbe.State.clearPending]
  | position position =>
      by_cases hposition : position = target
      · subst position
        have hvalue := resolveDeferredPositionValue_resolves target context resolved hresolved
        simp [cleanProbeObservation, installPositionValueAtProbe, hstate, hvalue,
          LazyRevealProbe.State.clearPending]
      · have hvalue : resolved.toDeferredContext.positionValue position =
            context.positionValue position := by
          unfold DeferredContext.positionValue
          rw [hstateValues]
          split
          · rfl
          · exact resolveDeferredPositionValue_preserves_other target position context resolved
              hposition hresolved
        simp [cleanProbeObservation, installPositionValueAtProbe, hstate, hvalue, hposition,
          LazyRevealProbe.State.clearPending]

theorem observationsAfterCandidate_materializedDeferredState_resolved
    (target : Position) (context : DeferredContext) (resolved : DeferredResolution)
    (hresolved : some resolved ∈ support
      (resolveDeferredPositionValue target context))
    (observations : List CleanProbeObservation) (candidate? : Option Probe) :
    observationsAfterCandidate
        (observations.map (installPositionValueAtProbe target resolved.output))
        (materializedDeferredState resolved.toDeferredContext) candidate? =
      (observationsAfterCandidate observations (materializedDeferredState context) candidate?).map
        (installPositionValueAtProbe target resolved.output) := by
  cases candidate? with
  | none => rfl
  | some candidate =>
      simp [observationsAfterCandidate,
        cleanProbeObservation_materializedDeferredState_resolved target context resolved hresolved]

theorem observationsAfterCandidate_eventEq_resolved_of_clean_of_avoids
    (target : Position) (context : DeferredContext) (resolved : DeferredResolution)
    (hresolved : some resolved ∈ support
      (resolveDeferredPositionValue target context))
    (observations : List CleanProbeObservation) (candidate? : Option Probe)
    (hclean : ∀ observation ∈
      observationsAfterCandidate observations (materializedDeferredState context) candidate?,
        ¬observation.ExistingHiddenHit)
    (havoid : CandidatesAvoidRoot target (truncateHash resolved.output)
      ((observationsAfterCandidate observations (materializedDeferredState context)
        candidate?).map CleanProbeObservation.toProbe)) :
    CleanProbeObservationsEventEq
      (observationsAfterCandidate
        (observations.map (installPositionValueAtProbe target resolved.output))
        (materializedDeferredState resolved.toDeferredContext) candidate?)
      (observationsAfterCandidate observations (materializedDeferredState context) candidate?) := by
  rw [observationsAfterCandidate_materializedDeferredState_resolved target context resolved
    hresolved]
  exact
    CleanProbeObservationsEventEq.map_installPositionValueAtProbe_of_clean_of_avoids target
      resolved.output _ hclean havoid

theorem observationsAfterCandidate_eventEq_resolved_current_of_clean_of_avoids
    (target : Position) (context : DeferredContext) (resolved : DeferredResolution)
    (hresolved : some resolved ∈ support
      (resolveDeferredPositionValue target context))
    (observations : List CleanProbeObservation) (candidate? : Option Probe)
    (hclean : ∀ observation ∈
      observationsAfterCandidate observations (materializedDeferredState context) candidate?,
        ¬observation.ExistingHiddenHit)
    (havoid : CandidatesAvoidRoot target (truncateHash resolved.output)
      ((observationsAfterCandidate observations (materializedDeferredState context)
        candidate?).map CleanProbeObservation.toProbe)) :
    CleanProbeObservationsEventEq
      (observationsAfterCandidate observations
        (materializedDeferredState resolved.toDeferredContext) candidate?)
      (observationsAfterCandidate observations (materializedDeferredState context) candidate?) := by
  cases candidate? with
  | none => exact CleanProbeObservationsEventEq.refl observations
  | some candidate =>
      apply List.rel_append (CleanProbeObservationsEventEq.refl observations)
      apply List.Forall₂.cons
      · rw [cleanProbeObservation_materializedDeferredState_resolved target context resolved
          hresolved]
        apply CleanProbeObservation.eventEq_installPositionValueAtProbe_of_clean_of_avoids
        · exact hclean _ (by simp [observationsAfterCandidate])
        · intro heq
          exact havoid _ (by simp [observationsAfterCandidate]) heq
      · exact .nil

def installPositionValueAtSnapshot
    (target : Position) (output : HashOutput)
    (snapshot : PlannedProbeSnapshot) : PlannedProbeSnapshot :=
  ⟨snapshot.probe,
    (completePrivatePosition target snapshot.context output).toDeferredContext⟩

@[simp] theorem installPositionValueAtSnapshot_toProbe
    (target : Position) (output : HashOutput) (snapshot : PlannedProbeSnapshot) :
    (installPositionValueAtSnapshot target output snapshot).toProbe = snapshot.toProbe := by
  rfl

theorem completePrivatePosition_eq_of_resolveDeferredPositionValue
    (target : Position) (context : DeferredContext) (resolved : DeferredResolution)
    (hresolved : some resolved ∈ support
      (resolveDeferredPositionValue target context)) :
    completePrivatePosition target context resolved.output = resolved := by
  have hstate := resolveDeferredPositionValue_state_eq_clearPending target context resolved
    hresolved
  have htarget := resolveDeferredPositionValue_installs target context resolved hresolved
  rcases resolved with ⟨⟨state, values⟩, output⟩
  simp only at hstate htarget ⊢
  subst state
  have hvalues : context.values.install target output = values := by
    funext position
    by_cases hposition : position = target
    · subst position
      simpa [DeferredStructuralValues.install] using htarget.symm
    · rw [DeferredStructuralValues.install, Function.update_of_ne hposition]
      exact (resolveDeferredPositionValue_preserves_other target position context
        ⟨⟨context.state.clearPending (.position target), values⟩, output⟩ hposition hresolved).symm
  simp [completePrivatePosition, hvalues]

theorem appendPlannedSnapshot_resolved
    (target : Position) (context : DeferredContext) (resolved : DeferredResolution)
    (hresolved : some resolved ∈ support
      (resolveDeferredPositionValue target context))
    (snapshots : List PlannedProbeSnapshot) (candidate? : Option Probe) :
    appendPlannedSnapshot
        (snapshots.map (installPositionValueAtSnapshot target resolved.output))
        candidate? resolved.toDeferredContext =
      (appendPlannedSnapshot snapshots candidate? context).map
        (installPositionValueAtSnapshot target resolved.output) := by
  have hcontext := congrArg DeferredResolution.toDeferredContext
    (completePrivatePosition_eq_of_resolveDeferredPositionValue target context resolved hresolved)
  cases candidate? with
  | none => rfl
  | some candidate =>
      simp [appendPlannedSnapshot, installPositionValueAtSnapshot, hcontext]

set_option maxRecDepth 100000 in
theorem evalDist_directDelayedSelectedRootIndicator_eq_of_selected_context
    (ordinal : Nat) (parameter : PublicParameter) (root : Digest)
    (ftsSecret : Index → FtsTree → FtsLeaf → Digest)
    (table : OtsSecretIndex → HashOutput) (target : Position) (rightRoot : Digest)
    (computation : OracleComp (OracleWorld + SigningSpec) α)
    (snapshots : List PlannedProbeSnapshot)
    (observations : List CleanProbeObservation)
    (left right : DeferredContext) (fuel : Nat) (cache : SplitHashCache)
    (hselected : ordinal < snapshots.length) :
    evalDist
        (directDelayedSelectedRootIndicator ordinal parameter root ftsSecret table target
          rightRoot computation snapshots observations left fuel cache) =
      evalDist
        (directDelayedSelectedRootIndicator ordinal parameter root ftsSecret table target
          rightRoot computation snapshots observations right fuel cache) := by
  rw [directDelayedSelectedRootIndicator_eq_selected ordinal parameter root ftsSecret table target
    rightRoot computation snapshots observations left fuel cache hselected]
  rw [directDelayedSelectedRootIndicator_eq_selected ordinal parameter root ftsSecret table target
    rightRoot computation snapshots observations right fuel cache hselected]

theorem evalDist_directDelayedSelectedRootIndicator_pure_eq_of_unselected_context
    (ordinal : Nat) (parameter : PublicParameter) (root : Digest)
    (ftsSecret : Index → FtsTree → FtsLeaf → Digest)
    (table : OtsSecretIndex → HashOutput) (target : Position) (rightRoot : Digest)
    (value : α) (snapshots : List PlannedProbeSnapshot)
    (observations : List CleanProbeObservation)
    (left right : DeferredContext) (fuel : Nat) (cache : SplitHashCache)
    (hselected : ¬ordinal < snapshots.length) :
    evalDist
        (directDelayedSelectedRootIndicator ordinal parameter root ftsSecret table target
          rightRoot (pure value) snapshots observations left fuel cache) =
      evalDist
        (directDelayedSelectedRootIndicator ordinal parameter root ftsSecret table target
          rightRoot (pure value) snapshots observations right fuel cache) := by
  simp [directDelayedSelectedRootIndicator, hselected]

set_option maxRecDepth 100000 in
theorem evalDist_negatedDirectDelayedSelectedRootIndicator_eq_of_selected_context
    (ordinal : Nat) (parameter : PublicParameter) (root : Digest)
    (ftsSecret : Index → FtsTree → FtsLeaf → Digest)
    (table : OtsSecretIndex → HashOutput) (target : Position) (rightRoot : Digest)
    (computation : OracleComp (OracleWorld + SigningSpec) α)
    (snapshots : List PlannedProbeSnapshot)
    (observations : List CleanProbeObservation)
    (left right : DeferredContext) (fuel : Nat) (cache : SplitHashCache)
    (hselected : ordinal < snapshots.length) :
    evalDist (Bool.not <$>
        directDelayedSelectedRootIndicator ordinal parameter root ftsSecret table target
          rightRoot computation snapshots observations left fuel cache) =
      evalDist (Bool.not <$>
        directDelayedSelectedRootIndicator ordinal parameter root ftsSecret table target
          rightRoot computation snapshots observations right fuel cache) := by
  rw [evalDist_map, evalDist_map,
    evalDist_directDelayedSelectedRootIndicator_eq_of_selected_context ordinal parameter root
      ftsSecret table target rightRoot computation snapshots observations left right fuel cache
      hselected]

theorem evalDist_negatedDirectDelayedSelectedRootIndicator_pure_eq_of_unselected_context
    (ordinal : Nat) (parameter : PublicParameter) (root : Digest)
    (ftsSecret : Index → FtsTree → FtsLeaf → Digest)
    (table : OtsSecretIndex → HashOutput) (target : Position) (rightRoot : Digest)
    (value : α) (snapshots : List PlannedProbeSnapshot)
    (observations : List CleanProbeObservation)
    (left right : DeferredContext) (fuel : Nat) (cache : SplitHashCache)
    (hselected : ¬ordinal < snapshots.length) :
    evalDist (Bool.not <$>
        directDelayedSelectedRootIndicator ordinal parameter root ftsSecret table target
          rightRoot (pure value) snapshots observations left fuel cache) =
      evalDist (Bool.not <$>
        directDelayedSelectedRootIndicator ordinal parameter root ftsSecret table target
          rightRoot (pure value) snapshots observations right fuel cache) := by
  rw [evalDist_map, evalDist_map,
    evalDist_directDelayedSelectedRootIndicator_pure_eq_of_unselected_context ordinal parameter
      root ftsSecret table target rightRoot value snapshots observations left right fuel cache
      hselected]

set_option maxRecDepth 100000 in
theorem evalDist_eagerDirectDelayedSelectedRootIndicator_uniform_eq
    (ordinal : Nat) (parameter : PublicParameter) (root : Digest)
    (ftsSecret : Index → FtsTree → FtsLeaf → Digest)
    (table : OtsSecretIndex → HashOutput) (target : Position) (rightRoot : Digest)
    (n : Nat) (next : Fin (n + 1) → OracleComp (OracleWorld + SigningSpec) α)
    (snapshots : List PlannedProbeSnapshot)
    (observations : List CleanProbeObservation)
    (context : DeferredContext) (fuel : Nat) (cache : SplitHashCache)
    (hselected : ¬ordinal < snapshots.length)
    (hvalid : context.Valid) (hcompletable : DeferredCompletable table context)
    (hpublished : PublishedValues context.state)
    (hnext : ∀ output,
      evalDist (eagerDirectDelayedSelectedRootIndicator ordinal parameter root ftsSecret table
        target rightRoot (next output) snapshots observations
        (canonicalizeMaterializedValues table context) fuel cache) =
      evalDist (directDelayedSelectedRootIndicator ordinal parameter root ftsSecret table target
        rightRoot (next output) snapshots observations
        (canonicalizeMaterializedValues table context) fuel cache)) :
    evalDist
        (eagerDirectDelayedSelectedRootIndicator ordinal parameter root ftsSecret table target
          rightRoot
          (liftM (OracleSpec.query (spec := OracleWorld + SigningSpec)
            (Sum.inl (Sum.inl n))) >>= next)
          snapshots observations context fuel cache) =
      evalDist
        (directDelayedSelectedRootIndicator ordinal parameter root ftsSecret table target
          rightRoot
          (liftM (OracleSpec.query (spec := OracleWorld + SigningSpec)
            (Sum.inl (Sum.inl n))) >>= next)
          snapshots observations context fuel cache) := by
  let uniform : ProbComp (Fin (n + 1)) := liftM (unifSpec.query n)
  let observe : DeferredContext → Nat → (Fin (n + 1) × SplitHashCache) →
      List PlannedProbeSnapshot → List CleanProbeObservation → ProbComp Bool :=
    fun nextContext remaining value laterSnapshots laterObservations ↦
      directDelayedSelectedRootIndicator ordinal parameter root ftsSecret table target rightRoot
        (next value.1) laterSnapshots laterObservations nextContext remaining value.2
  unfold eagerDirectDelayedSelectedRootIndicator
  simp only [hselected, ↓reduceIte]
  rw [directDelayedSelectedRootIndicator_uniform_eq ordinal parameter root ftsSecret table target
    rightRoot n next snapshots observations context fuel cache hselected]
  calc
    _ = evalDist (resolveDeferredPositionValue target context >>= fun resolved ↦
          match resolved with
          | none => pure false
          | some resolved =>
              runDirectResolvedWitnessFromTable resolved.toDeferredContext fuel table
                  ((splitUniformImpl n).run cache) >>=
                finishDirectDelayedSelectedRootIndicator
                  (canonicalizeDirectDelayedSelectedRootIndicator table observe)
                  snapshots observations) := by
      apply evalDist_bind_congr
      intro resolved hresolved
      cases resolved with
      | none => rfl
      | some resolved =>
          simpa only using congrArg evalDist
            (directDelayedSelectedRootIndicator_uniform_eq ordinal parameter root ftsSecret table
              target rightRoot n next snapshots observations resolved.toDeferredContext fuel cache
              hselected)
    _ = evalDist (resolveDeferredPositionValue target context >>= fun resolved ↦
          uniform >>= fun output ↦
            match resolved with
            | none => pure false
            | some resolved =>
                canonicalizeDirectDelayedSelectedRootIndicator table observe
                  resolved.toDeferredContext fuel (output, cache) snapshots observations) := by
      simp_rw [runDirectResolvedWitnessFromTable_splitUniformImpl]
      apply evalDist_bind_congr
      intro resolved _hresolved
      cases resolved with
      | none =>
          exact (OracleComp.DeferredSampling.evalDist_bind_const_neverFails uniform
            (by simp [uniform]) (pure false)).symm
      | some resolved =>
          simp [finishDirectDelayedSelectedRootIndicator, uniform]
    _ = evalDist (uniform >>= fun output ↦
          resolveDeferredPositionValue target context >>= fun resolved ↦
            match resolved with
            | none => pure false
            | some resolved =>
                canonicalizeDirectDelayedSelectedRootIndicator table observe
                  resolved.toDeferredContext fuel (output, cache) snapshots observations) := by
      exact OracleComp.DeferredSampling.evalDist_bind_comm
        (resolveDeferredPositionValue target context) uniform
        (fun resolved output ↦
          match resolved with
          | none => pure false
          | some resolved =>
              canonicalizeDirectDelayedSelectedRootIndicator table observe
                resolved.toDeferredContext fuel (output, cache) snapshots observations)
    _ = evalDist (uniform >>= fun output ↦
          canonicalizeDirectDelayedSelectedRootIndicator table observe context fuel
            (output, cache) snapshots observations) := by
      apply evalDist_bind_congr
      intro output _houtput
      apply evalDist_resolveDeferredPositionValue_then_canonicalizeDirectDelayed table target
        observe context fuel (output, cache) snapshots observations hvalid hcompletable hpublished
      simpa [eagerDirectDelayedSelectedRootIndicator, hselected, observe] using hnext output
    _ = _ := by
      simp [uniform, observe, runDirectResolvedWitnessFromTable_splitUniformImpl,
        finishDirectDelayedSelectedRootIndicator]

set_option maxRecDepth 100000 in
theorem evalDist_eagerDirectDelayedSelectedRootIndicator_signing_eq
    (ordinal : Nat) (parameter : PublicParameter) (root : Digest)
    (ftsSecret : Index → FtsTree → FtsLeaf → Digest)
    (table : OtsSecretIndex → HashOutput) (target : Position) (rightRoot : Digest)
    (message : Message)
    (next : Option Signature → OracleComp (OracleWorld + SigningSpec) α)
    (snapshots : List PlannedProbeSnapshot)
    (observations : List CleanProbeObservation)
    (context : DeferredContext) (fuel : Nat) (cache : SplitHashCache)
    (hselected : ¬ordinal < snapshots.length)
    (hvalid : context.Valid) (hcompletable : DeferredCompletable table context)
    [ObserverSynchronized table
      (negatedDirectDelayedObserve
        (fun nextContext remaining (value : Option Signature × SplitHashCache)
            laterSnapshots laterObservations ↦
          directDelayedSelectedRootIndicator ordinal parameter root ftsSecret table target
            rightRoot (next value.1) laterSnapshots laterObservations nextContext remaining
            value.2)
        snapshots observations)]
    [ObserverPositionNeutral table
      (negatedDirectDelayedObserve
        (fun nextContext remaining (value : Option Signature × SplitHashCache)
            laterSnapshots laterObservations ↦
          directDelayedSelectedRootIndicator ordinal parameter root ftsSecret table target
            rightRoot (next value.1) laterSnapshots laterObservations nextContext remaining
            value.2)
        snapshots observations)] :
    evalDist
        (eagerDirectDelayedSelectedRootIndicator ordinal parameter root ftsSecret table target
          rightRoot
          (liftM (OracleSpec.query (spec := OracleWorld + SigningSpec) (Sum.inr message)) >>= next)
          snapshots observations context fuel cache) =
      evalDist
        (directDelayedSelectedRootIndicator ordinal parameter root ftsSecret table target
          rightRoot
          (liftM (OracleSpec.query (spec := OracleWorld + SigningSpec) (Sum.inr message)) >>= next)
          snapshots observations context fuel cache) := by
  let observe := fun nextContext remaining (value : Option Signature × SplitHashCache)
      laterSnapshots laterObservations ↦
    directDelayedSelectedRootIndicator ordinal parameter root ftsSecret table target rightRoot
      (next value.1) laterSnapshots laterObservations nextContext remaining value.2
  rw [directDelayedSelectedRootIndicator_signing_eq ordinal parameter root ftsSecret table target
    rightRoot message next snapshots observations context fuel cache hselected]
  unfold eagerDirectDelayedSelectedRootIndicator
  simp only [hselected, ↓reduceIte]
  calc
    _ = evalDist (resolveDeferredPositionValue target context >>= fun resolved ↦
          match resolved with
          | none => pure false
          | some resolved =>
              runDirectResolvedWitnessFromTable resolved.toDeferredContext fuel table
                  ((maskedSign parameter root ftsSecret message).run cache) >>=
                finishDirectDelayedSelectedRootIndicator
                  (canonicalizeDirectDelayedSelectedRootIndicator table observe)
                  snapshots observations) := by
        apply evalDist_bind_congr
        intro resolved hresolved
        cases resolved with
        | none => rfl
        | some resolved =>
            simpa only [observe] using congrArg evalDist
              (directDelayedSelectedRootIndicator_signing_eq ordinal parameter root ftsSecret table
                target rightRoot message next snapshots observations resolved.toDeferredContext
                fuel cache hselected)
    _ = _ := evalDist_resolve_then_runDirectWitness_finish_false table target observe snapshots
      observations ((maskedSign parameter root ftsSecret message).run cache) context fuel hvalid
      hcompletable

set_option maxRecDepth 100000 in
theorem relTriple_directDelayed_eagerDirectDelayed_hash_selected
    (ordinal : Nat) (parameter : PublicParameter) (root : Digest)
    (ftsSecret : Index → FtsTree → FtsLeaf → Digest)
    (table : OtsSecretIndex → HashOutput) (target : Position) (rightRoot : Digest)
    (input : HashInput)
    (next : HashOutput → OracleComp (OracleWorld + SigningSpec) α)
    (snapshots : List PlannedProbeSnapshot)
    (observations : List CleanProbeObservation)
    (context : DeferredContext) (fuel : Nat) (cache : SplitHashCache)
    (hbefore : ¬ordinal < snapshots.length)
    (hselected : ordinal <
      (appendPlannedSnapshot snapshots
        (rootAwareCandidateForPlan? parameter input
          (purePlanProbingHashQuery parameter input context.state)) context).length) :
    RelTriple
      (directDelayedSelectedRootIndicator ordinal parameter root ftsSecret table target
          rightRoot
          (liftM (OracleSpec.query (spec := OracleWorld + SigningSpec)
            (Sum.inl (Sum.inr input))) >>= next)
          snapshots observations context fuel cache)
      (eagerDirectDelayedSelectedRootIndicator ordinal parameter root ftsSecret table target
          rightRoot
          (liftM (OracleSpec.query (spec := OracleWorld + SigningSpec)
            (Sum.inl (Sum.inr input))) >>= next)
          snapshots observations context fuel cache)
      (EqRel Bool) := by
  classical
  let candidate? := rootAwareCandidateForPlan? parameter input
    (purePlanProbingHashQuery parameter input context.state)
  let nextSnapshots := appendPlannedSnapshot snapshots candidate? context
  have hnowSelected : ordinal < nextSnapshots.length := by
    simpa [nextSnapshots, candidate?] using hselected
  have hcandidateExists : ∃ candidate, candidate? = some candidate := by
    cases hcandidate : candidate? with
    | none =>
        exfalso
        apply hbefore
        simpa [nextSnapshots, hcandidate, appendPlannedSnapshot] using hnowSelected
    | some candidate => exact ⟨candidate, rfl⟩
  obtain ⟨candidate, hcandidate⟩ := hcandidateExists
  have hnextSnapshots : nextSnapshots =
      snapshots ++ [(⟨candidate, context⟩ : PlannedProbeSnapshot)] := by
    simp [nextSnapshots, hcandidate, appendPlannedSnapshot]
  have hordinal : snapshots.length = ordinal := by
    rw [hnextSnapshots] at hnowSelected
    simp only [List.length_append, List.length_singleton] at hnowSelected
    omega
  have hget : nextSnapshots.get ⟨ordinal, hnowSelected⟩ =
      (⟨candidate, context⟩ : PlannedProbeSnapshot) := by
    subst ordinal
    simp [nextSnapshots, appendPlannedSnapshot, hcandidate, List.get_eq_getElem]
  rw [directDelayedSelectedRootIndicator_hash_eq_selected ordinal parameter root ftsSecret table
    target rightRoot input next snapshots observations context fuel cache hbefore hselected]
  rw [show (appendPlannedSnapshot snapshots
      (rootAwareCandidateForPlan? parameter input
        (purePlanProbingHashQuery parameter input context.state)) context).get
        ⟨ordinal, hselected⟩ = (⟨candidate, context⟩ : PlannedProbeSnapshot) by
      simpa [nextSnapshots, candidate?] using hget]
  unfold eagerDirectDelayedSelectedRootIndicator
  simp only [hbefore, ↓reduceIte]
  unfold delayedSelectedRootIndicator
  have hresolve := SphincsSecurity.Concrete.FtsProbeSimulation.relTriple_and_left_support
    (relTriple_refl (resolveDeferredPositionValue target context))
    (fun resolved => resolved ∈ support (resolveDeferredPositionValue target context))
    (fun resolved hresolved => hresolved)
  apply relTriple_bind hresolve
  intro leftResolved rightResolved hrelation
  obtain ⟨rfl, hresolved⟩ := hrelation
  cases leftResolved with
  | none => exact relTriple_pure_pure rfl
  | some resolved =>
      have hvalues := resolveDeferredPositionValue_preserves_state_values target context resolved
        hresolved
      have hplan : purePlanProbingHashQuery parameter input resolved.state =
          purePlanProbingHashQuery parameter input context.state :=
        purePlanProbingHashQuery_eq_of_values_eq hvalues parameter input
      have hcandidateResolved : rootAwareCandidateForPlan? parameter input
          (purePlanProbingHashQuery parameter input resolved.state) = some candidate := by
        rw [hplan]
        simpa [candidate?] using hcandidate
      have hselectedResolved : ordinal <
          (appendPlannedSnapshot snapshots
            (rootAwareCandidateForPlan? parameter input
              (purePlanProbingHashQuery parameter input resolved.state))
            resolved.toDeferredContext).length := by
        simp [appendPlannedSnapshot, hcandidateResolved, ← hordinal]
      have hgetResolved :
          (appendPlannedSnapshot snapshots
            (rootAwareCandidateForPlan? parameter input
              (purePlanProbingHashQuery parameter input resolved.state))
            resolved.toDeferredContext).get ⟨ordinal, hselectedResolved⟩ =
              (⟨candidate, resolved.toDeferredContext⟩ : PlannedProbeSnapshot) := by
        subst ordinal
        simp [appendPlannedSnapshot, hcandidateResolved, List.get_eq_getElem]
      simp only
      rw [directDelayedSelectedRootIndicator_hash_eq_selected ordinal parameter root ftsSecret table
        target rightRoot input next snapshots observations resolved.toDeferredContext fuel cache
        hbefore hselectedResolved]
      rw [hgetResolved]
      unfold delayedSelectedRootIndicator
      rw [resolveDeferredPositionValue_of_resolved target context resolved hresolved]
      simp only [pure_bind]
      have hcandidates :
          (appendPlannedSnapshot snapshots
              (rootAwareCandidateForPlan? parameter input
                (purePlanProbingHashQuery parameter input resolved.state))
              resolved.toDeferredContext).map PlannedProbeSnapshot.toProbe =
            (appendPlannedSnapshot snapshots
              (rootAwareCandidateForPlan? parameter input
                (purePlanProbingHashQuery parameter input context.state))
              context).map PlannedProbeSnapshot.toProbe := by
        have hcandidateBase : rootAwareCandidateForPlan? parameter input
            (purePlanProbingHashQuery parameter input context.state) = some candidate := by
          simpa [candidate?] using hcandidate
        simp [appendPlannedSnapshot, hcandidateResolved, hcandidateBase]
      rw [hcandidates]
      let selection : PrivateOrdinalSelection :=
        ⟨candidate, context,
          (appendPlannedSnapshot snapshots
            (rootAwareCandidateForPlan? parameter input
              (purePlanProbingHashQuery parameter input context.state)) context).map
                PlannedProbeSnapshot.toProbe⟩
      change RelTriple
        (if CandidatesAvoidRoots target (truncateHash resolved.output) rightRoot
            (selection.candidates.take ordinal) then
          (successfulObservedRootComparisonIndicator table ordinal target ∘
              fun observed => (observed, rightRoot)) <$>
            observedMaterializedBoundary parameter root ftsSecret
              (liftM (OracleSpec.query (spec := OracleWorld + SigningSpec)
                (Sum.inl (Sum.inr input))) >>= next)
              observations (materializedDeferredState resolved.toDeferredContext) fuel table cache
        else pure false)
        (if CandidatesAvoidRoots target (truncateHash resolved.output) rightRoot
            (selection.candidates.take ordinal) then
          (successfulObservedRootComparisonIndicator table ordinal target ∘
              fun observed => (observed, rightRoot)) <$>
            observedMaterializedBoundary parameter root ftsSecret
              (liftM (OracleSpec.query (spec := OracleWorld + SigningSpec)
                (Sum.inl (Sum.inr input))) >>= next)
              observations (materializedDeferredState resolved.toDeferredContext) fuel table cache
        else pure false)
        (EqRel Bool)
      by_cases hsafe : CandidatesAvoidRoots target (truncateHash resolved.output) rightRoot
          (selection.candidates.take ordinal)
      · simp only [hsafe, ↓reduceIte]
        exact relTriple_refl _
      · simp only [hsafe, ↓reduceIte]
        exact relTriple_pure_pure rfl

theorem evalDist_eagerDirectDelayedSelectedRootIndicator_hash_eq_selected
    (ordinal : Nat) (parameter : PublicParameter) (root : Digest)
    (ftsSecret : Index → FtsTree → FtsLeaf → Digest)
    (table : OtsSecretIndex → HashOutput) (target : Position) (rightRoot : Digest)
    (input : HashInput)
    (next : HashOutput → OracleComp (OracleWorld + SigningSpec) α)
    (snapshots : List PlannedProbeSnapshot)
    (observations : List CleanProbeObservation)
    (context : DeferredContext) (fuel : Nat) (cache : SplitHashCache)
    (hbefore : ¬ordinal < snapshots.length)
    (hselected : ordinal <
      (appendPlannedSnapshot snapshots
        (rootAwareCandidateForPlan? parameter input
          (purePlanProbingHashQuery parameter input context.state)) context).length) :
    evalDist
        (eagerDirectDelayedSelectedRootIndicator ordinal parameter root ftsSecret table target
          rightRoot
          (liftM (OracleSpec.query (spec := OracleWorld + SigningSpec)
            (Sum.inl (Sum.inr input))) >>= next)
          snapshots observations context fuel cache) =
      evalDist
        (directDelayedSelectedRootIndicator ordinal parameter root ftsSecret table target
          rightRoot
          (liftM (OracleSpec.query (spec := OracleWorld + SigningSpec)
            (Sum.inl (Sum.inr input))) >>= next)
          snapshots observations context fuel cache) := by
  exact (evalDist_eq_of_relTriple_eqRel
    (relTriple_directDelayed_eagerDirectDelayed_hash_selected ordinal parameter root ftsSecret
      table target rightRoot input next snapshots observations context fuel cache hbefore
      hselected)).symm

set_option maxHeartbeats 2000000 in
set_option maxRecDepth 1000000 in
theorem evalDist_eagerDirectDelayedSelectedRootIndicator_hash_eq_not_selected_of_trace
    (ordinal : Nat) (parameter : PublicParameter) (root : Digest)
    (ftsSecret : Index → FtsTree → FtsLeaf → Digest)
    (table : OtsSecretIndex → HashOutput) (target : Position) (rightRoot : Digest)
    (input : HashInput)
    (next : HashOutput → OracleComp (OracleWorld + SigningSpec) α)
    (snapshots : List PlannedProbeSnapshot)
    (observations : List CleanProbeObservation)
    (context : DeferredContext) (fuel : Nat) (cache : SplitHashCache)
    (hbefore : ¬ordinal < snapshots.length)
    (hnotSelected : ¬ordinal <
      (appendPlannedSnapshot snapshots
        (rootAwareCandidateForPlan? parameter input
          (purePlanProbingHashQuery parameter input context.state)) context).length)
    (hvalid : context.Valid) (hcompletable : DeferredCompletable table context)
    [ObserverSynchronized table
      (negatedDirectDelayedObserve
        (fun nextContext remaining (value : HashOutput × SplitHashCache)
            laterSnapshots laterObservations ↦
          directDelayedSelectedRootIndicator ordinal parameter root ftsSecret table target
            rightRoot (next value.1) laterSnapshots laterObservations nextContext remaining
            value.2)
        (appendPlannedSnapshot snapshots
          (rootAwareCandidateForPlan? parameter input
            (purePlanProbingHashQuery parameter input context.state)) context)
        (observationsAfterCandidate observations (materializedDeferredState context)
          (rootAwareCandidateForPlan? parameter input
            (purePlanProbingHashQuery parameter input context.state))))]
    [ObserverPositionNeutral table
      (negatedDirectDelayedObserve
        (fun nextContext remaining (value : HashOutput × SplitHashCache)
            laterSnapshots laterObservations ↦
          directDelayedSelectedRootIndicator ordinal parameter root ftsSecret table target
            rightRoot (next value.1) laterSnapshots laterObservations nextContext remaining
            value.2)
        (appendPlannedSnapshot snapshots
          (rootAwareCandidateForPlan? parameter input
            (purePlanProbingHashQuery parameter input context.state)) context)
        (observationsAfterCandidate observations (materializedDeferredState context)
          (rootAwareCandidateForPlan? parameter input
            (purePlanProbingHashQuery parameter input context.state))))]
    (htrace : ∀ (resolved : DeferredResolution)
        (_hresolved : some resolved ∈ support
          (resolveDeferredPositionValue target context)),
      evalDist
          (runDirectResolvedWitnessFromTable resolved.toDeferredContext fuel table
              ((probingHashQueryAfterPlan parameter input
                (purePlanProbingHashQuery parameter input context.state)).run cache) >>=
            finishDirectDelayedSelectedRootIndicator
              (canonicalizeDirectDelayedSelectedRootIndicator table
                (fun nextContext remaining value laterSnapshots laterObservations ↦
                  directDelayedSelectedRootIndicator ordinal parameter root ftsSecret table target
                    rightRoot (next value.1) laterSnapshots laterObservations nextContext remaining
                    value.2))
              (appendPlannedSnapshot snapshots
                (rootAwareCandidateForPlan? parameter input
                  (purePlanProbingHashQuery parameter input context.state))
                resolved.toDeferredContext)
              (observationsAfterCandidate observations
                (materializedDeferredState resolved.toDeferredContext)
                (rootAwareCandidateForPlan? parameter input
                  (purePlanProbingHashQuery parameter input context.state)))) =
        evalDist
          (runDirectResolvedWitnessFromTable resolved.toDeferredContext fuel table
              ((probingHashQueryAfterPlan parameter input
                (purePlanProbingHashQuery parameter input context.state)).run cache) >>=
            finishDirectDelayedSelectedRootIndicator
              (canonicalizeDirectDelayedSelectedRootIndicator table
                (fun nextContext remaining value laterSnapshots laterObservations ↦
                  directDelayedSelectedRootIndicator ordinal parameter root ftsSecret table target
                    rightRoot (next value.1) laterSnapshots laterObservations nextContext remaining
                    value.2))
              (appendPlannedSnapshot snapshots
                (rootAwareCandidateForPlan? parameter input
                  (purePlanProbingHashQuery parameter input context.state)) context)
              (observationsAfterCandidate observations (materializedDeferredState context)
                (rootAwareCandidateForPlan? parameter input
                  (purePlanProbingHashQuery parameter input context.state))))) :
    evalDist
        (eagerDirectDelayedSelectedRootIndicator ordinal parameter root ftsSecret table target
          rightRoot
          (liftM (OracleSpec.query (spec := OracleWorld + SigningSpec)
            (Sum.inl (Sum.inr input))) >>= next)
          snapshots observations context fuel cache) =
      evalDist
        (directDelayedSelectedRootIndicator ordinal parameter root ftsSecret table target
          rightRoot
          (liftM (OracleSpec.query (spec := OracleWorld + SigningSpec)
            (Sum.inl (Sum.inr input))) >>= next)
          snapshots observations context fuel cache) := by
  rw [directDelayedSelectedRootIndicator_hash_eq_not_selected ordinal parameter root ftsSecret table
    target rightRoot input next snapshots observations context fuel cache hbefore hnotSelected]
  unfold eagerDirectDelayedSelectedRootIndicator
  simp only [hbefore, ↓reduceIte]
  calc
    _ = evalDist (resolveDeferredPositionValue target context >>= fun resolved ↦
          match resolved with
          | none => pure false
          | some resolved =>
              runDirectResolvedWitnessFromTable resolved.toDeferredContext fuel table
                  ((probingHashQueryAfterPlan parameter input
                    (purePlanProbingHashQuery parameter input context.state)).run cache) >>=
                finishDirectDelayedSelectedRootIndicator
                  (canonicalizeDirectDelayedSelectedRootIndicator table
                    (fun nextContext remaining value laterSnapshots laterObservations ↦
                      directDelayedSelectedRootIndicator ordinal parameter root ftsSecret table
                        target rightRoot (next value.1) laterSnapshots laterObservations nextContext
                        remaining value.2))
                  (appendPlannedSnapshot snapshots
                    (rootAwareCandidateForPlan? parameter input
                      (purePlanProbingHashQuery parameter input context.state)) context)
                  (observationsAfterCandidate observations (materializedDeferredState context)
                    (rootAwareCandidateForPlan? parameter input
                      (purePlanProbingHashQuery parameter input context.state)))) := by
        apply evalDist_bind_congr
        intro resolved hresolved
        cases resolved with
        | none => rfl
        | some resolved =>
            have hvalues := resolveDeferredPositionValue_preserves_state_values target context
              resolved hresolved
            have hplan : purePlanProbingHashQuery parameter input resolved.state =
                purePlanProbingHashQuery parameter input context.state :=
              purePlanProbingHashQuery_eq_of_values_eq hvalues parameter input
            have hnotSelectedResolved : ¬ordinal <
                (appendPlannedSnapshot snapshots
                  (rootAwareCandidateForPlan? parameter input
                    (purePlanProbingHashQuery parameter input resolved.state))
                  resolved.toDeferredContext).length := by
              rw [hplan]
              have hlength :
                  (appendPlannedSnapshot snapshots
                      (rootAwareCandidateForPlan? parameter input
                        (purePlanProbingHashQuery parameter input context.state))
                      resolved.toDeferredContext).length =
                    (appendPlannedSnapshot snapshots
                      (rootAwareCandidateForPlan? parameter input
                        (purePlanProbingHashQuery parameter input context.state)) context).length := by
                cases rootAwareCandidateForPlan? parameter input
                    (purePlanProbingHashQuery parameter input context.state) <;>
                  simp [appendPlannedSnapshot]
              rw [hlength]
              exact hnotSelected
            simp only
            rw [directDelayedSelectedRootIndicator_hash_eq_not_selected ordinal parameter root
              ftsSecret table target rightRoot input next snapshots observations
              resolved.toDeferredContext fuel cache hbefore hnotSelectedResolved]
            rw [hplan]
            exact htrace resolved hresolved
    _ = _ := evalDist_resolve_then_runDirectWitness_finish_false table target
      (fun nextContext remaining (value : HashOutput × SplitHashCache)
          laterSnapshots laterObservations ↦
        directDelayedSelectedRootIndicator ordinal parameter root ftsSecret table target rightRoot
          (next value.1) laterSnapshots laterObservations nextContext remaining value.2)
      (appendPlannedSnapshot snapshots
        (rootAwareCandidateForPlan? parameter input
          (purePlanProbingHashQuery parameter input context.state)) context)
      (observationsAfterCandidate observations (materializedDeferredState context)
        (rootAwareCandidateForPlan? parameter input
          (purePlanProbingHashQuery parameter input context.state)))
      ((probingHashQueryAfterPlan parameter input
        (purePlanProbingHashQuery parameter input context.state)).run cache)
      context fuel hvalid hcompletable

set_option maxHeartbeats 2000000 in
set_option maxRecDepth 1000000 in
theorem evalDist_eagerDirectDelayedSelectedRootIndicator_hash_eq_not_selected_of_clean_avoids
    (ordinal : Nat) (parameter : PublicParameter) (root : Digest)
    (ftsSecret : Index → FtsTree → FtsLeaf → Digest)
    (table : OtsSecretIndex → HashOutput) (target : Position) (rightRoot : Digest)
    (input : HashInput)
    (next : HashOutput → OracleComp (OracleWorld + SigningSpec) α)
    (snapshots : List PlannedProbeSnapshot)
    (observations : List CleanProbeObservation)
    (context : DeferredContext) (fuel : Nat) (cache : SplitHashCache)
    (hbefore : ¬ordinal < snapshots.length)
    (hnotSelected : ¬ordinal <
      (appendPlannedSnapshot snapshots
        (rootAwareCandidateForPlan? parameter input
          (purePlanProbingHashQuery parameter input context.state)) context).length)
    (hvalid : context.Valid) (hcompletable : DeferredCompletable table context)
    [ObserverSynchronized table
      (negatedDirectDelayedObserve
        (fun nextContext remaining (value : HashOutput × SplitHashCache)
            laterSnapshots laterObservations ↦
          directDelayedSelectedRootIndicator ordinal parameter root ftsSecret table target
            rightRoot (next value.1) laterSnapshots laterObservations nextContext remaining
            value.2)
        (appendPlannedSnapshot snapshots
          (rootAwareCandidateForPlan? parameter input
            (purePlanProbingHashQuery parameter input context.state)) context)
        (observationsAfterCandidate observations (materializedDeferredState context)
          (rootAwareCandidateForPlan? parameter input
            (purePlanProbingHashQuery parameter input context.state))))]
    [ObserverPositionNeutral table
      (negatedDirectDelayedObserve
        (fun nextContext remaining (value : HashOutput × SplitHashCache)
            laterSnapshots laterObservations ↦
          directDelayedSelectedRootIndicator ordinal parameter root ftsSecret table target
            rightRoot (next value.1) laterSnapshots laterObservations nextContext remaining
            value.2)
        (appendPlannedSnapshot snapshots
          (rootAwareCandidateForPlan? parameter input
            (purePlanProbingHashQuery parameter input context.state)) context)
        (observationsAfterCandidate observations (materializedDeferredState context)
          (rootAwareCandidateForPlan? parameter input
            (purePlanProbingHashQuery parameter input context.state))))]
    (hclean : ∀ observation ∈
      observationsAfterCandidate observations (materializedDeferredState context)
        (rootAwareCandidateForPlan? parameter input
          (purePlanProbingHashQuery parameter input context.state)),
        ¬observation.ExistingHiddenHit)
    (havoid : ∀ resolved : DeferredResolution,
      some resolved ∈ support (resolveDeferredPositionValue target context) →
        CandidatesAvoidRoot target (truncateHash resolved.output)
          ((observationsAfterCandidate observations (materializedDeferredState context)
            (rootAwareCandidateForPlan? parameter input
              (purePlanProbingHashQuery parameter input context.state))).map
                CleanProbeObservation.toProbe)) :
    evalDist
        (eagerDirectDelayedSelectedRootIndicator ordinal parameter root ftsSecret table target
          rightRoot
          (liftM (OracleSpec.query (spec := OracleWorld + SigningSpec)
            (Sum.inl (Sum.inr input))) >>= next)
          snapshots observations context fuel cache) =
      evalDist
        (directDelayedSelectedRootIndicator ordinal parameter root ftsSecret table target
          rightRoot
          (liftM (OracleSpec.query (spec := OracleWorld + SigningSpec)
            (Sum.inl (Sum.inr input))) >>= next)
          snapshots observations context fuel cache) := by
  apply evalDist_eagerDirectDelayedSelectedRootIndicator_hash_eq_not_selected_of_trace ordinal
    parameter root ftsSecret table target rightRoot input next snapshots observations context fuel
    cache hbefore hnotSelected hvalid hcompletable
  intro resolved hresolved
  have hvalues := resolveDeferredPositionValue_preserves_state_values target context resolved
    hresolved
  have hplan : purePlanProbingHashQuery parameter input resolved.state =
      purePlanProbingHashQuery parameter input context.state :=
    purePlanProbingHashQuery_eq_of_values_eq hvalues parameter input
  let candidate? := rootAwareCandidateForPlan? parameter input
    (purePlanProbingHashQuery parameter input context.state)
  let leftSnapshots := appendPlannedSnapshot snapshots candidate? resolved.toDeferredContext
  let rightSnapshots := appendPlannedSnapshot snapshots candidate? context
  let leftObservations := observationsAfterCandidate observations
    (materializedDeferredState resolved.toDeferredContext) candidate?
  let rightObservations := observationsAfterCandidate observations
    (materializedDeferredState context) candidate?
  have hsnapshots : leftSnapshots.map PlannedProbeSnapshot.toProbe =
      rightSnapshots.map PlannedProbeSnapshot.toProbe := by
    cases hcandidate : candidate? <;>
      simp [leftSnapshots, rightSnapshots, appendPlannedSnapshot, hcandidate]
  have hlength : leftSnapshots.length = rightSnapshots.length :=
    plannedProbeSnapshots_length_eq_of_toProbe_eq hsnapshots
  have hrightBefore : ¬ordinal < rightSnapshots.length := by
    simpa [rightSnapshots, candidate?] using hnotSelected
  have hleftBefore : ¬ordinal < leftSnapshots.length := by
    rwa [hlength]
  have htrace : CleanProbeObservationsEventEq leftObservations rightObservations := by
    apply observationsAfterCandidate_eventEq_resolved_current_of_clean_of_avoids target context
      resolved hresolved observations candidate?
    · simpa [rightObservations, candidate?] using hclean
    · simpa [rightObservations, candidate?] using havoid resolved hresolved
  apply evalDist_bind_congr
  intro result _hresult
  cases result with
  | stoppedFuel => rfl
  | stoppedOrdinary => rfl
  | stoppedPrivate witness => rfl
  | done result =>
      simp only [finishDirectDelayedSelectedRootIndicator,
        canonicalizeDirectDelayedSelectedRootIndicator]
      split
      · rfl
      · split
        · split
          · exact evalDist_directDelayedSelectedRootIndicator_eq_of_eventEq ordinal parameter root
              ftsSecret table target rightRoot (next result.value.1) leftSnapshots rightSnapshots
              leftObservations rightObservations
              (canonicalizeMaterializedValues table result.context) result.remaining result.value.2
              hleftBefore hrightBefore hsnapshots htrace
          · rfl
        · rfl

end SphincsSecurity.Concrete.OtsProbeSimulation
