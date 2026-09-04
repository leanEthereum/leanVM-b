import SphincsSecurity.Proof.OtsProbeResolvedBoundaryPrivateWitnessOrdinalRootGlobalClassificationStoppedRootAdaptiveNormalizeLift

/-! Structural synchronization and target-neutrality for adaptive normalization. -/

namespace SphincsSecurity.Concrete.OtsProbeSimulation

open OracleComp OracleSpec
open OracleComp.ProgramLogic.Relational

set_option maxHeartbeats 8000000 in
set_option maxRecDepth 1000000 in
theorem negatedDirectDelayedComputationObserve_observerLaws
    (ordinal : Nat) (parameter : PublicParameter) (root : Digest)
    (ftsSecret : Index → FtsTree → FtsLeaf → Digest)
    (table : OtsSecretIndex → HashOutput) (target : Position) (rightRoot : Digest)
    (computation : OracleComp (OracleWorld + SigningSpec) α) :
    ∀ (snapshots : List PlannedProbeSnapshot)
      (observations : List CleanProbeObservation),
      snapshots.length ≤ ordinal →
      observations.map CleanProbeObservation.toProbe =
        snapshots.map PlannedProbeSnapshot.toProbe →
      (∀ observation ∈ observations, ¬observation.ExistingHiddenHit) →
      ObserverSynchronized table
          (negatedDirectDelayedComputationObserve ordinal parameter root ftsSecret table target
            rightRoot computation snapshots observations) ∧
        ObserverPositionNeutralAt table target
          (negatedDirectDelayedComputationObserve ordinal parameter root ftsSecret table target
            rightRoot computation snapshots observations) := by
  intro snapshots observations hbefore haligned hclean
  induction computation using OracleComp.inductionOn generalizing snapshots observations with
  | pure value =>
      exact ⟨
        negatedDirectDelayedComputationObserve_pure_observerSynchronized ordinal parameter root
          ftsSecret table target rightRoot value snapshots observations hbefore,
        negatedDirectDelayedComputationObserve_pure_observerPositionNeutralAt ordinal parameter
          root ftsSecret table target target rightRoot value snapshots observations hbefore⟩
  | query_bind query next ih =>
      cases query with
      | inl worldQuery =>
          cases worldQuery with
          | inl n =>
              change Fin (n + 1) → OracleComp (OracleWorld + SigningSpec) α at next
              have hnext : ∀ output,
                  ObserverSynchronized table
                      (negatedDirectDelayedComputationObserve ordinal parameter root ftsSecret
                        table target rightRoot (next output) snapshots observations) ∧
                    ObserverPositionNeutralAt table target
                      (negatedDirectDelayedComputationObserve ordinal parameter root ftsSecret
                        table target rightRoot (next output) snapshots observations) :=
                fun output ↦ ih output snapshots observations hbefore haligned hclean
              exact ⟨
                negatedDirectDelayedComputationObserve_uniform_observerSynchronized ordinal
                  parameter root ftsSecret table target rightRoot n next snapshots observations
                  hbefore (fun output ↦ (hnext output).1),
                negatedDirectDelayedComputationObserve_uniform_observerPositionNeutralAt ordinal
                  parameter root ftsSecret table target rightRoot target n next snapshots
                  observations hbefore (fun output ↦ (hnext output).2)⟩
          | inr input =>
              change HashOutput → OracleComp (OracleWorld + SigningSpec) α at next
              have hnext : ∀ output laterSnapshots laterObservations,
                  laterSnapshots.length ≤ ordinal →
                  laterObservations.map CleanProbeObservation.toProbe =
                    laterSnapshots.map PlannedProbeSnapshot.toProbe →
                  (∀ observation ∈ laterObservations,
                    ¬observation.ExistingHiddenHit) →
                  ObserverSynchronized table
                      (negatedDirectDelayedComputationObserve ordinal parameter root ftsSecret
                        table target rightRoot (next output) laterSnapshots laterObservations) ∧
                    ObserverPositionNeutralAt table target
                      (negatedDirectDelayedComputationObserve ordinal parameter root ftsSecret
                        table target rightRoot (next output) laterSnapshots laterObservations) :=
                fun output laterSnapshots laterObservations hlaterBefore hlaterAligned
                    hlaterClean ↦
                  ih output laterSnapshots laterObservations hlaterBefore hlaterAligned hlaterClean
              exact ⟨
                negatedDirectDelayedComputationObserve_hash_observerSynchronized ordinal parameter
                  root ftsSecret table target rightRoot input next snapshots observations hbefore
                  haligned hclean
                  (fun output laterSnapshots laterObservations hlaterBefore hlaterAligned
                      hlaterClean ↦
                    (hnext output laterSnapshots laterObservations hlaterBefore hlaterAligned
                      hlaterClean).1),
                negatedDirectDelayedComputationObserve_hash_observerPositionNeutralAt ordinal
                  parameter root ftsSecret table target rightRoot input next snapshots observations
                  hbefore haligned hclean
                  (fun output laterSnapshots laterObservations hlaterBefore hlaterAligned
                      hlaterClean ↦
                    (hnext output laterSnapshots laterObservations hlaterBefore hlaterAligned
                      hlaterClean).2)⟩
      | inr message =>
          change Option Signature → OracleComp (OracleWorld + SigningSpec) α at next
          have hnext : ∀ output,
              ObserverSynchronized table
                  (negatedDirectDelayedComputationObserve ordinal parameter root ftsSecret table
                    target rightRoot (next output) snapshots observations) ∧
                ObserverPositionNeutralAt table target
                  (negatedDirectDelayedComputationObserve ordinal parameter root ftsSecret table
                    target rightRoot (next output) snapshots observations) :=
            fun output ↦ ih output snapshots observations hbefore haligned hclean
          exact ⟨
            negatedDirectDelayedComputationObserve_signing_observerSynchronized ordinal parameter
              root ftsSecret table target rightRoot message next snapshots observations hbefore
              (fun output ↦ (hnext output).1),
            negatedDirectDelayedComputationObserve_signing_observerPositionNeutralAt ordinal
              parameter root ftsSecret table target rightRoot target message next snapshots
              observations hbefore (fun output ↦ (hnext output).2)⟩

set_option maxRecDepth 100000 in
theorem evalDist_resolveDeferredPositionValue_then_observe_eq_of_synchronized
    (table : OtsSecretIndex → HashOutput) (position : Position)
    {observe : DeferredContext → Nat → α → ProbComp Bool}
    [ObserverSynchronized table observe]
    (left right : DeferredContext) (fuel : Nat) (value : α)
    (hcontext : FinalizationContextEq table (some left) (some right))
    (hvalues : left.state.values = right.state.values)
    (hrevealed : left.state.revealed = right.state.revealed) :
    evalDist (resolveDeferredPositionValue position left >>= fun resolved ↦
      match resolved with
      | none => pure true
      | some resolved => observe resolved.toDeferredContext fuel value) =
      evalDist (resolveDeferredPositionValue position right >>= fun resolved ↦
        match resolved with
        | none => pure true
        | some resolved => observe resolved.toDeferredContext fuel value) := by
  rcases hcontext with ⟨hview, hleftValid, hrightValid, hleftCompletable⟩
  have hresolved := relTriple_resolveDeferredPositionValue_of_finalizationViewEq table position
    left right hview hleftValid hrightValid hleftCompletable
  have hresolvedLeft :=
    SphincsSecurity.Concrete.FtsProbeSimulation.relTriple_and_left_support hresolved
      (fun result => result ∈ support (resolveDeferredPositionValue position left))
      (fun result hresult => hresult)
  have hresolvedBoth :=
    SphincsSecurity.Concrete.FtsProbeSimulation.relTriple_and_right_support hresolvedLeft
  apply evalDist_eq_of_relTriple_eqRel
  apply relTriple_bind hresolvedBoth
  intro leftResolved rightResolved hrelation
  rcases hrelation with ⟨⟨hrelation, hleftSupport⟩, hrightSupport⟩
  cases leftResolved with
  | none =>
      cases rightResolved with
      | none => exact relTriple_pure_pure rfl
      | some rightResolved => simp [FinalizationResolutionEq] at hrelation
  | some leftResolved =>
      cases rightResolved with
      | none => simp [FinalizationResolutionEq] at hrelation
      | some rightResolved =>
          apply relTriple_eqRel_of_evalDist_eq
          apply ObserverSynchronized.eq_of_synchronized
            (table := table) (observe := observe)
          · exact ⟨hrelation.2.1, hrelation.2.2.1, hrelation.2.2.2.1,
              hrelation.2.2.2.2⟩
          · rw [resolveDeferredPositionValue_preserves_state_values position left leftResolved
                hleftSupport,
              resolveDeferredPositionValue_preserves_state_values position right rightResolved
                hrightSupport]
            exact hvalues
          · rw [resolveDeferredPositionValue_state_eq_clearPending position left leftResolved
                hleftSupport,
              resolveDeferredPositionValue_state_eq_clearPending position right rightResolved
                hrightSupport]
            simpa [LazyRevealProbe.State.clearPending] using hrevealed

set_option maxRecDepth 100000 in
theorem evalDist_resolveDeferredPositionValue_then_observe_any_at
    (table : OtsSecretIndex → HashOutput) (position : Position)
    {observe : DeferredContext → Nat → α → ProbComp Bool}
    [ObserverSynchronized table observe]
    (context : DeferredContext) (fuel : Nat) (value : α)
    (hvalid : context.Valid) (hcompletable : DeferredCompletable table context)
    (hneutral : ObserverPositionNeutralAt table position observe) :
    evalDist (resolveDeferredPositionValue position context >>= fun resolved ↦
      match resolved with
      | none => pure true
      | some resolved => observe resolved.toDeferredContext fuel value) =
      evalDist (observe context fuel value) := by
  let ensured : DeferredContext :=
    { context with state := context.state.ensure (.position position) }
  have hensuredValid : ensured.Valid := hvalid.ensure (.position position)
  have hensuredCompletable : DeferredCompletable table ensured :=
    hcompletable.ensure (.position position)
  have hstarts := startTableAgrees_of_deferredCompletable hcompletable
  have hensuredStarts : StartTableAgrees ensured.state table :=
    hstarts.ensure (.position position)
  have hview : FinalizationViewEq table context ensured :=
    finalizationViewEq_of_deferredCompletion_iff hvalid hensuredValid hstarts hensuredStarts rfl
      hcompletable (fun _ => Iff.rfl)
  have hcontext : FinalizationContextEq table (some context) (some ensured) :=
    ⟨hview, hvalid, hensuredValid, hcompletable⟩
  have hcontextSymm : FinalizationContextEq table (some ensured) (some context) :=
    ⟨hview.symm, hensuredValid, hvalid, hensuredCompletable⟩
  calc
    _ = evalDist (resolveDeferredPositionValue position ensured >>= fun resolved ↦
          match resolved with
          | none => pure true
          | some resolved => observe resolved.toDeferredContext fuel value) :=
      evalDist_resolveDeferredPositionValue_then_observe_eq_of_synchronized table position
        context ensured fuel value hcontext rfl rfl
    _ = evalDist (observe ensured fuel value) :=
      hneutral ensured fuel value hensuredValid hensuredCompletable
        (by simp [ensured, LazyRevealProbe.State.ensure])
    _ = _ :=
      ObserverSynchronized.eq_of_synchronized ensured context fuel value hcontextSymm rfl rfl

set_option maxHeartbeats 8000000 in
set_option maxRecDepth 1000000 in
theorem evalDist_eagerDirectDelayedSelectedRootIndicator_eq
    (ordinal : Nat) (parameter : PublicParameter) (root : Digest)
    (ftsSecret : Index → FtsTree → FtsLeaf → Digest)
    (table : OtsSecretIndex → HashOutput) (target : Position) (rightRoot : Digest)
    (computation : OracleComp (OracleWorld + SigningSpec) α)
    (snapshots : List PlannedProbeSnapshot)
    (observations : List CleanProbeObservation)
    (context : DeferredContext) (fuel : Nat) (cache : SplitHashCache)
    (hbefore : snapshots.length ≤ ordinal)
    (haligned : observations.map CleanProbeObservation.toProbe =
      snapshots.map PlannedProbeSnapshot.toProbe)
    (hclean : ∀ observation ∈ observations, ¬observation.ExistingHiddenHit)
    (hvalid : context.Valid) (hcompletable : DeferredCompletable table context) :
    evalDist
        (eagerDirectDelayedSelectedRootIndicator ordinal parameter root ftsSecret table target
          rightRoot computation snapshots observations context fuel cache) =
      evalDist
        (directDelayedSelectedRootIndicator ordinal parameter root ftsSecret table target
          rightRoot computation snapshots observations context fuel cache) := by
  have hnotSelected : ¬ordinal < snapshots.length := by omega
  let observe := negatedDirectDelayedComputationObserve ordinal parameter root ftsSecret table
    target rightRoot computation snapshots observations
  have hlaws := negatedDirectDelayedComputationObserve_observerLaws ordinal parameter root
    ftsSecret table target rightRoot computation snapshots observations hbefore haligned hclean
  letI : ObserverSynchronized table observe := by
    simpa only [observe] using hlaws.1
  have hneutral : ObserverPositionNeutralAt table target observe := by
    simpa only [observe] using hlaws.2
  apply evalDist_eq_of_complement_eq
  unfold eagerDirectDelayedSelectedRootIndicator
  rw [if_neg hnotSelected, map_bind]
  calc
    _ = evalDist (resolveDeferredPositionValue target context >>= fun resolved ↦
          match resolved with
          | none => pure true
          | some resolved => observe resolved.toDeferredContext fuel cache) := by
        apply evalDist_bind_congr
        intro resolved _hresolved
        cases resolved <;> rfl
    _ = evalDist (observe context fuel cache) :=
      evalDist_resolveDeferredPositionValue_then_observe_any_at table target context fuel cache
        hvalid hcompletable hneutral
    _ = _ := by rfl

end SphincsSecurity.Concrete.OtsProbeSimulation
