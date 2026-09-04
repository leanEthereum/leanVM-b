import SphincsSecurity.Proof.OtsProbeResolvedBoundaryPrivateWitnessOrdinalRootGlobalClassificationStoppedRootAdaptiveProductionCommonInitial

/-!
# Commonizing resolved production fibers

The resolved target-specific detailed selector is coupled to the single target-independent
detailed selector. The deferred target resolution becomes one preloaded sample, while its hidden
cache entry is removed through the ordinary-cache quotient.
-/

namespace SphincsSecurity.Concrete.OtsProbeSimulation

open OracleComp OracleSpec ENNReal
open OracleComp.ProgramLogic.Relational

theorem probEvent_bind_le_bind_of_forall_le_of_invariant
    {mx : ProbComp α} {left : α → ProbComp β} {right : α → ProbComp γ}
    {leftEvent : β → Prop} {rightEvent : γ → Prop} (invariant : α → Prop)
    (hinvariant : ∀ value ∈ support mx, invariant value)
    (hstep : ∀ value, invariant value →
      Pr[leftEvent | left value] ≤ Pr[rightEvent | right value]) :
    Pr[leftEvent | mx >>= left] ≤ Pr[rightEvent | mx >>= right] := by
  apply probEvent_bind_le_bind_of_forall_le
  intro value hvalue
  exact hstep value (hinvariant value hvalue)

theorem materializedDeferredState_freshResolution_rel_preload
    (state : LazyRevealProbe.State Coordinate) (target : Position) (output : HashOutput)
    (hvalue : state.values (.position target) = none) (hpending : state.pending = ∅) :
    PermissiveStateRel
      (materializedDeferredState
        { state := state.clearPending (.position target)
          values := (directDeferredValues state).install target output })
      (preloadPositionValue target output state) := by
  rcases state with ⟨pending, values, revealed, ensured⟩
  simp only at hvalue hpending
  subst pending
  constructor
  · funext coordinate
    cases coordinate with
    | chainStart lay tree leafIdx chainIdx =>
        simp [materializedDeferredState, LazyRevealProbe.State.clearPending,
          LazyRevealProbe.State.pendingAway, DeferredStructuralValues.install,
          DeferredContext.positionValue, preloadPositionValue]
    | position position =>
        by_cases heq : position = target
        · subst position
          simp [materializedDeferredState, LazyRevealProbe.State.clearPending,
            LazyRevealProbe.State.pendingAway,
            DeferredStructuralValues.install, DeferredContext.positionValue,
            preloadPositionValue, hvalue]
        · have hcoordinate : Coordinate.position position ≠ Coordinate.position target := by
            simpa using heq
          simp [materializedDeferredState, LazyRevealProbe.State.clearPending,
            LazyRevealProbe.State.pendingAway, directDeferredValues,
            DeferredStructuralValues.install, DeferredContext.positionValue,
            preloadPositionValue, heq, hcoordinate]
          cases values (Coordinate.position position) <;> rfl
  · rfl

set_option maxRecDepth 100000 in
theorem relTriple_resolvedInstalledPermissiveDetailedSelection_common_afterRootResult
    (ordinal : Nat) (adversary : Adversary) (parameter : PublicParameter)
    (ftsSecret : Index → FtsTree → FtsLeaf → Digest)
    (target : Position) (rootResult : CleanRunResult (Digest × SplitHashCache))
    (hvalue : rootResult.state.values (.position target) = none)
    (hpending : rootResult.state.pending = ∅) :
    RelTriple
      (resolvedInstalledPermissiveDetailedSelectionAfterRootResult ordinal adversary parameter
        ftsSecret target rootResult)
      (permissiveDetailedSelectionAfterRootResult ordinal adversary parameter ftsSecret rootResult)
      (fun left right =>
        permissivePrivateOrdinalSelectionUnrevealedLayerRootPosition? left.2 = some target →
          permissivePrivateOrdinalSelectionUnrevealedLayerRootPosition? right = some target) := by
  unfold resolvedInstalledPermissiveDetailedSelectionAfterRootResult
    permissiveDetailedSelectionAfterRootResult
  rw [resolveDeferredPositionValue_fresh target (directDeferredContext rootResult.state)]
  · have hhit : ∀ output, ¬rootResult.state.hitAt (.position target) output := by
      intro output
      simp [LazyRevealProbe.State.hitAt, LazyRevealProbe.State.pendingAt, hpending]
    simp only [directDeferredContext, hhit, ↓reduceIte, bind_assoc, pure_bind]
    let computation :=
      retainedGameRestComputation adversary ⟨rootResult.value.1, parameter⟩
    let sampled := LazyRevealProbe.sampleHashOutput >>= fun output =>
      permissiveDetailedRootAwareOrdinalSelection ordinal parameter rootResult.value.1 ftsSecret
        computation [] (preloadPositionValue target output rootResult.state)
        rootResult.remaining rootResult.table rootResult.value.2
    have hperOutput (output : HashOutput) :
        RelTriple
          (permissiveDetailedRootAwareOrdinalSelection ordinal parameter rootResult.value.1
              ftsSecret computation []
              (materializedDeferredState
                { state := rootResult.state.clearPending (.position target)
                  values := (directDeferredValues rootResult.state).install target output })
              rootResult.remaining rootResult.table
              (replaceHiddenRootCache target output rootResult.value.2) >>= fun selection =>
            pure (truncateHash output, selection))
          (permissiveDetailedRootAwareOrdinalSelection ordinal parameter rootResult.value.1
            ftsSecret computation [] (preloadPositionValue target output rootResult.state)
            rootResult.remaining rootResult.table rootResult.value.2)
          (fun left right =>
            permissivePrivateOrdinalSelectionUnrevealedLayerRootPosition? left.2 = some target →
              permissivePrivateOrdinalSelectionUnrevealedLayerRootPosition? right =
                some target) := by
      let resolvedState := materializedDeferredState
        { state := rootResult.state.clearPending (.position target)
          values := (directDeferredValues rootResult.state).install target output }
      have hcache :=
        relTriple_permissiveDetailedRootAwareOrdinalSelection_of_ordinaryCacheEq ordinal parameter
          rootResult.value.1 ftsSecret computation [] resolvedState rootResult.remaining
          rootResult.table (replaceHiddenRootCache target output rootResult.value.2)
          rootResult.value.2
          (ordinaryQueryCache_replaceHiddenRootCache target output rootResult.value.2)
      have hstate :=
        relTriple_permissiveDetailedRootAwareOrdinalSelection_targetFiber_of_stateRel ordinal
          parameter rootResult.value.1 ftsSecret computation [] resolvedState
          (preloadPositionValue target output rootResult.state) rootResult.remaining
          rootResult.table rootResult.value.2 target
          (materializedDeferredState_freshResolution_rel_preload rootResult.state target output
            hvalue hpending)
      have hglued := SphincsSecurity.relTriple_trans_exists hcache hstate
      have hselection := relTriple_post_mono hglued (by
        intro left right hrelation
        obtain ⟨middle, hmiddle, hfiber⟩ := hrelation
        subst middle
        exact hfiber)
      have hlift : RelTriple
          (permissiveDetailedRootAwareOrdinalSelection ordinal parameter rootResult.value.1
              ftsSecret computation [] resolvedState rootResult.remaining rootResult.table
              (replaceHiddenRootCache target output rootResult.value.2) >>= fun selection =>
            pure (truncateHash output, selection))
          (permissiveDetailedRootAwareOrdinalSelection ordinal parameter rootResult.value.1
              ftsSecret computation [] (preloadPositionValue target output rootResult.state)
              rootResult.remaining rootResult.table rootResult.value.2 >>= fun selection =>
            pure selection)
          (fun left right =>
            permissivePrivateOrdinalSelectionUnrevealedLayerRootPosition? left.2 = some target →
              permissivePrivateOrdinalSelectionUnrevealedLayerRootPosition? right =
                some target) := by
        apply relTriple_bind hselection
        intro left right hrelation
        exact relTriple_pure_pure hrelation
      simpa only [bind_pure, resolvedState] using hlift
    have hbridge : RelTriple
        (LazyRevealProbe.sampleHashOutput >>= fun output =>
          permissiveDetailedRootAwareOrdinalSelection ordinal parameter rootResult.value.1
              ftsSecret computation []
              (materializedDeferredState
                { state := rootResult.state.clearPending (.position target)
                  values := (directDeferredValues rootResult.state).install target output })
              rootResult.remaining rootResult.table
              (replaceHiddenRootCache target output rootResult.value.2) >>= fun selection =>
            pure (truncateHash output, selection))
        sampled
        (fun left right =>
          permissivePrivateOrdinalSelectionUnrevealedLayerRootPosition? left.2 = some target →
            permissivePrivateOrdinalSelectionUnrevealedLayerRootPosition? right = some target) := by
      apply relTriple_bind (relTriple_refl LazyRevealProbe.sampleHashOutput)
      intro leftOutput rightOutput heq
      subst rightOutput
      exact hperOutput leftOutput
    have hsampling :=
      relTriple_sample_preload_permissiveDetailedRootAwareOrdinalSelection ordinal parameter
        rootResult.value.1 ftsSecret computation [] rootResult.state rootResult.remaining
        rootResult.table rootResult.value.2 target hvalue
    have hglued := SphincsSecurity.relTriple_trans_exists hbridge hsampling
    apply relTriple_post_mono hglued
    intro left right hrelation hleft
    obtain ⟨middle, hfirst, hsecond⟩ := hrelation
    exact hsecond (hfirst hleft)
  · simpa [directDeferredContext] using hvalue
  · simpa [directDeferredContext, directDeferredValues] using hvalue

set_option maxHeartbeats 4000000 in
set_option maxRecDepth 100000 in
theorem probEvent_resolvedInstalledPermissiveDetailedSelectionExperiment_fiber_le_common
    (ordinal : Nat) (adversary : Adversary) (parameter : PublicParameter)
    (ftsSecret : Index → FtsTree → FtsLeaf → Digest)
    (target : Position) (hroot : IsLayerRoot target)
    (hparent : ∃ parent, Position.parentOf target = some parent)
    (fuel : Nat) (table : OtsSecretIndex → HashOutput) :
    Pr[fun result =>
        permissivePrivateOrdinalSelectionUnrevealedLayerRootPosition? result.2 = some target |
      resolvedInstalledPermissiveDetailedSelectionExperimentAfterTable ordinal adversary
        parameter ftsSecret target fuel table] ≤
      Pr[fun selection =>
          permissivePrivateOrdinalSelectionUnrevealedLayerRootPosition? selection = some target |
        permissiveDetailedSelectionExperimentAfterTable ordinal adversary parameter ftsSecret fuel
          table] := by
  unfold resolvedInstalledPermissiveDetailedSelectionExperimentAfterTable
    permissiveDetailedSelectionExperimentAfterTable
  apply probEvent_bind_le_bind_of_forall_le_of_invariant
    (invariant := InitialRootOptionFacts target)
  · exact initialRootOptionFacts_of_mem target hroot hparent fuel table
  · intro rootResult hinitial
    cases rootResult with
    | none =>
        simp [permissivePrivateOrdinalSelectionUnrevealedLayerRootPosition?]
    | some rootResult =>
        have hrel : RelTriple
            (resolvedInstalledPermissiveDetailedSelectionAfterRootResult ordinal adversary parameter
              ftsSecret target rootResult)
            (permissiveDetailedSelectionAfterRootResult ordinal adversary parameter ftsSecret
              rootResult)
            (fun left right =>
              permissivePrivateOrdinalSelectionUnrevealedLayerRootPosition? left.2 = some target →
                permissivePrivateOrdinalSelectionUnrevealedLayerRootPosition? right = some target) :=
          relTriple_resolvedInstalledPermissiveDetailedSelection_common_afterRootResult ordinal
            adversary parameter ftsSecret target rootResult hinitial.1 hinitial.2.2
        apply probEvent_le_of_relTriple
          (p := fun result =>
            permissivePrivateOrdinalSelectionUnrevealedLayerRootPosition? result.2 = some target)
          (q := fun selection =>
            permissivePrivateOrdinalSelectionUnrevealedLayerRootPosition? selection = some target)
          hrel
        intro left right hrelation hleft
        exact hrelation hleft

set_option maxRecDepth 100000 in
theorem probEvent_materializedRootAwareProduction_le_commonDetailedFiber
    (ordinal : Nat) (adversary : Adversary) (parameter : PublicParameter)
    (ftsSecret : Index → FtsTree → FtsLeaf → Digest)
    (target : Position) (hroot : IsLayerRoot target)
    (hparent : ∃ parent, Position.parentOf target = some parent)
    (fuel : Nat) (table : OtsSecretIndex → HashOutput) :
    Pr[fun result => materializedOrdinalSelectionAt target result.2 |
      materializedRootAwareOrdinalProductionExperimentAfterTable ordinal adversary parameter
        ftsSecret target fuel table] ≤
      Pr[fun selection =>
          permissivePrivateOrdinalSelectionUnrevealedLayerRootPosition? selection = some target |
        permissiveDetailedSelectionExperimentAfterTable ordinal adversary parameter ftsSecret fuel
          table] := by
  calc
    _ ≤ Pr[fun result =>
          permissivePrivateOrdinalSelectionUnrevealedLayerRootPosition? result.2 = some target |
        resolvedInstalledPermissiveDetailedSelectionExperimentAfterTable ordinal adversary
          parameter ftsSecret target fuel table] :=
      probEvent_materializedRootAwareProduction_le_resolvedPermissiveDetailed ordinal adversary
        parameter ftsSecret target hroot hparent fuel table
    _ ≤ _ :=
      probEvent_resolvedInstalledPermissiveDetailedSelectionExperiment_fiber_le_common ordinal
        adversary parameter ftsSecret target hroot hparent fuel table

set_option maxHeartbeats 4000000 in
set_option maxRecDepth 100000 in
theorem probEvent_successfulDoomedFirstRootFiber_le_commonDetailedFiber
    (ordinal : Nat) (adversary : Adversary) (parameter : PublicParameter)
    (table : OtsSecretIndex → HashOutput)
    (ftsSecret : Index → FtsTree → FtsLeaf → Digest)
    (q : Nat) (target : Position) (hroot : IsLayerRoot target)
    (hparent : ∃ parent, Position.parentOf target = some parent)
    (hordinal : ordinal < q)
    (hfuel : 2 * q < Fintype.card Digest)
    (hbound : ∀ root,
      (simulateQ
        (SphincsSecurity.expandedAdversaryImpl
          (⟨parameter, root, tableOtsSecret (extendStartTable table), ftsSecret⟩ : SecretKey))
        (retainedGameRestComputation adversary ⟨root, parameter⟩)).IsQueryBoundP
          (fun query => query matches Sum.inr _) q)
    (hq : q ≤ 2 ^ securityBits) :
    Pr[fun observed =>
        ObservedCleanRunOption.SuccessfulDoomedFirstRootHitAtTarget
          table ordinal target observed |
      observedMaterializedRetainedRunFromTable adversary parameter ftsSecret (2 * q) table] ≤
      Pr[fun selection =>
          permissivePrivateOrdinalSelectionUnrevealedLayerRootPosition? selection = some target |
        permissiveDetailedSelectionExperimentAfterTable ordinal adversary parameter ftsSecret
          (2 * q) table] *
        (2 * ((2 ^ digestBits : Nat) : ENNReal)⁻¹) := by
  calc
    _ ≤ Pr[fun result => materializedOrdinalSelectionAt target result.2 |
          materializedRootAwareOrdinalProductionExperimentAfterTable ordinal adversary parameter
            ftsSecret target (2 * q) table] *
          (2 * ((2 ^ digestBits : Nat) : ENNReal)⁻¹) :=
      probEvent_successfulDoomedFirstRootFiber_le_two_mul_production ordinal adversary parameter
        table ftsSecret q target hroot hparent hordinal hfuel hbound hq
    _ ≤ _ := by
      gcongr
      exact probEvent_materializedRootAwareProduction_le_commonDetailedFiber ordinal adversary
        parameter ftsSecret target hroot hparent (2 * q) table

end SphincsSecurity.Concrete.OtsProbeSimulation
