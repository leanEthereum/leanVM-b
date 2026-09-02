import SphincsSecurity.Proof.OtsProbeResolvedBoundaryPrivateWitnessOrdinalRootGlobalClassificationStoppedRootAdaptiveAfterRoot
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
  apply evalDist_bind_congr
  intro resolved hresolved
  cases resolved with
  | none => rfl
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
      rfl

end SphincsSecurity.Concrete.OtsProbeSimulation
