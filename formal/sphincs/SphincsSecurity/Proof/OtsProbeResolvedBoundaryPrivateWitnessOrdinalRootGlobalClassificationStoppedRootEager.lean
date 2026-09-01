import SphincsSecurity.Proof.OtsProbeResolvedBoundaryPrivateWitnessOrdinalRootGlobalClassificationStoppedRootComparison

/-!
# Eager layer-root selection

The source selector may learn its selected layer root lazily during an earlier signer or structural
computation. The materialized comparison samples that root before the retained run. This file
connects the two schedules while retaining the installed root in the comparison state.
-/

namespace SphincsSecurity.Concrete.OtsProbeSimulation

open OracleComp OracleSpec ENNReal
open OracleComp.ProgramLogic.Relational

noncomputable def candidateFinalizationObserve
    (table : OtsSecretIndex → HashOutput)
    (context : DeferredContext) (fuel : Nat) (candidate : Probe) : ProbComp Bool :=
  runResolvedObserve (resolvedFinalizationObserve table) context (fuel + 1) table (do
    (probe candidate).run emptySplitHashCache)

theorem evalDist_candidateFinalizationObserve_eq_true_of_goodForRoots
    (table : OtsSecretIndex → HashOutput)
    (selection : PrivateOrdinalSelection) (fuel : Nat)
    (target : Position) (output : HashOutput) (rightRoot : Digest) (ordinal : Nat)
    (hvalid : selection.context.Valid)
    (hcompletable : DeferredCompletable table selection.context)
    (hgood : selection.GoodForRoots target output rightRoot ordinal) :
    evalDist (candidateFinalizationObserve table selection.context fuel selection.candidate) =
      evalDist (pure true : ProbComp Bool) := by
  have hstarts := startTableAgrees_of_deferredCompletable hcompletable
  obtain ⟨completion, hcompletion⟩ := hcompletable
  have hdoomed : ¬DeferredCompletable table
      { selection.context with
        state := selection.context.state.addPending
          (.position target) (truncateHash output) } := by
    simpa using not_congr
      (deferredCompletable_addPending_position_iff target output (truncateHash output)
        hcompletion hgood.2.2.2.1)
  unfold candidateFinalizationObserve
  rw [show selection.candidate = ⟨.position target, truncateHash output⟩ from hgood.1]
  unfold probe
  rw [StateT.run_liftM, LazyRevealProbe.probeQuery,
    runResolvedObserve, runResolvedFromTable_probe_query_bind]
  simp only [hgood.2.2.1, ↓reduceIte]
  exact evalDist_runResolvedObserve_eq_true_of_not_completable_auto
    { selection.context with
      state := selection.context.state.addPending (.position target) (truncateHash output) }
    fuel table (pure ((), emptySplitHashCache))
    (hvalid.valuesConsistent.addPending (.position target) (truncateHash output))
    (hstarts.addPending (.position target) (truncateHash output)) hdoomed

instance candidateFinalizationObserve_observerDooms
    (table : OtsSecretIndex → HashOutput) :
    ObserverDooms table (candidateFinalizationObserve table) where
  eq_true context fuel candidate hconsistent hstarts hdoomed := by
    exact evalDist_runResolvedObserve_eq_true_of_not_completable_auto
      (observe := resolvedFinalizationObserve table) context (fuel + 1) table
      ((probe candidate).run emptySplitHashCache) hconsistent hstarts hdoomed

instance candidateFinalizationObserve_observerSynchronized
    (table : OtsSecretIndex → HashOutput) :
    ObserverSynchronized table (candidateFinalizationObserve table) where
  eq_of_synchronized left right fuel candidate hcontext hvalues hrevealed := by
    exact evalDist_runResolvedObserve_eq_of_finalizationSynchronized
      (observe := resolvedFinalizationObserve table)
      ((probe candidate).run emptySplitHashCache) left right (fuel + 1) table hcontext
      hvalues hrevealed

instance candidateFinalizationObserve_observerPositionNeutral
    (table : OtsSecretIndex → HashOutput) :
    ObserverPositionNeutral table (candidateFinalizationObserve table) where
  eq_resolve position context fuel candidate hvalid hcompletable hensured := by
    exact evalDist_resolveDeferredPositionValue_then_runResolvedObserve_auto position
      (observe := resolvedFinalizationObserve table)
      ((probe candidate).run emptySplitHashCache) context (fuel + 1) table hvalid
      hcompletable hensured

noncomputable def ordinalRootFinalizationObserve
    (table : OtsSecretIndex → HashOutput) (target : Position)
    (rightRoot : Digest) (ordinal : Nat)
    (context : DeferredContext) (fuel : Nat) (candidates : List Probe) : ProbComp Bool := by
  classical
  exact if hselected : ordinal < candidates.length then
    let candidate := candidates.get ⟨ordinal, hselected⟩
    if candidate.coordinate = .position target ∧
        CandidatesAvoidRoot target rightRoot (candidates.take ordinal) then
      candidateFinalizationObserve table context fuel candidate
    else resolvedFinalizationObserve table context fuel ()
  else resolvedFinalizationObserve table context fuel ()

instance ordinalRootFinalizationObserve_observerDooms
    (table : OtsSecretIndex → HashOutput) (target : Position)
    (rightRoot : Digest) (ordinal : Nat) (candidates : List Probe) :
    ObserverDooms table
      (fun context fuel (_value : Unit) =>
        ordinalRootFinalizationObserve table target rightRoot ordinal context fuel candidates) where
  eq_true context fuel _value hconsistent hstarts hdoomed := by
    unfold ordinalRootFinalizationObserve
    by_cases hselected : ordinal < candidates.length
    · simp only [hselected, ↓reduceDIte]
      by_cases hgate :
          (candidates.get ⟨ordinal, hselected⟩).coordinate = .position target ∧
            CandidatesAvoidRoot target rightRoot (candidates.take ordinal)
      · simp only [hgate]
        exact ObserverDooms.eq_true
          (table := table) (observe := candidateFinalizationObserve table)
          context fuel _ hconsistent hstarts hdoomed
      · simp only [hgate]
        exact ObserverDooms.eq_true
          (table := table) (observe := resolvedFinalizationObserve table)
          context fuel () hconsistent hstarts hdoomed
    · simp only [hselected, ↓reduceDIte]
      exact ObserverDooms.eq_true
        (table := table) (observe := resolvedFinalizationObserve table)
        context fuel () hconsistent hstarts hdoomed

instance ordinalRootFinalizationObserve_observerSynchronized
    (table : OtsSecretIndex → HashOutput) (target : Position)
    (rightRoot : Digest) (ordinal : Nat) (candidates : List Probe) :
    ObserverSynchronized table
      (fun context fuel (_value : Unit) =>
        ordinalRootFinalizationObserve table target rightRoot ordinal context fuel candidates) where
  eq_of_synchronized left right fuel _value hcontext hvalues hrevealed := by
    unfold ordinalRootFinalizationObserve
    by_cases hselected : ordinal < candidates.length
    · simp only [hselected, ↓reduceDIte]
      by_cases hgate :
          (candidates.get ⟨ordinal, hselected⟩).coordinate = .position target ∧
            CandidatesAvoidRoot target rightRoot (candidates.take ordinal)
      · simp only [hgate]
        exact ObserverSynchronized.eq_of_synchronized
          (table := table) (observe := candidateFinalizationObserve table)
          left right fuel _ hcontext hvalues hrevealed
      · simp only [hgate]
        exact ObserverSynchronized.eq_of_synchronized
          (table := table) (observe := resolvedFinalizationObserve table)
          left right fuel () hcontext hvalues hrevealed
    · simp only [hselected, ↓reduceDIte]
      exact ObserverSynchronized.eq_of_synchronized
        (table := table) (observe := resolvedFinalizationObserve table)
        left right fuel () hcontext hvalues hrevealed

instance ordinalRootFinalizationObserve_observerPositionNeutral
    (table : OtsSecretIndex → HashOutput) (target : Position)
    (rightRoot : Digest) (ordinal : Nat) (candidates : List Probe) :
    ObserverPositionNeutral table
      (fun context fuel (_value : Unit) =>
        ordinalRootFinalizationObserve table target rightRoot ordinal context fuel candidates) where
  eq_resolve position context fuel _value hvalid hcompletable hensured := by
    unfold ordinalRootFinalizationObserve
    by_cases hselected : ordinal < candidates.length
    · simp only [hselected, ↓reduceDIte]
      by_cases hgate :
          (candidates.get ⟨ordinal, hselected⟩).coordinate = .position target ∧
            CandidatesAvoidRoot target rightRoot (candidates.take ordinal)
      · simp only [hgate]
        exact ObserverPositionNeutral.eq_resolve
          (table := table) (observe := candidateFinalizationObserve table)
          position context fuel _ hvalid hcompletable hensured
      · simp only [hgate]
        exact ObserverPositionNeutral.eq_resolve
          (table := table) (observe := resolvedFinalizationObserve table)
          position context fuel () hvalid hcompletable hensured
    · simp only [hselected, ↓reduceDIte]
      exact ObserverPositionNeutral.eq_resolve
        (table := table) (observe := resolvedFinalizationObserve table)
        position context fuel () hvalid hcompletable hensured

noncomputable def directBoundaryPrivateOrdinalFinalizationRisk
    (ordinal : Nat) (parameter : PublicParameter) (root : Digest)
    (ftsSecret : Index → FtsTree → FtsLeaf → Digest)
    (target : Position) (rightRoot : Digest)
    (computation : OracleComp (OracleWorld + SigningSpec) α)
    (candidates : List Probe) (context : DeferredContext) (fuel : Nat)
    (table : OtsSecretIndex → HashOutput) (cache : SplitHashCache) : ProbComp Bool := by
  classical
  exact OracleComp.construct
    (C := fun _ : OracleComp (OracleWorld + SigningSpec) α =>
      List Probe → DeferredContext → Nat → (OtsSecretIndex → HashOutput) →
        SplitHashCache → ProbComp Bool)
    (fun _value candidates context fuel table _cache =>
      ordinalRootFinalizationObserve table target rightRoot ordinal context fuel candidates)
    (fun query _next recursivelyRun candidates context fuel table cache =>
      if hselected : ordinal < candidates.length then
        ordinalRootFinalizationObserve table target rightRoot ordinal context fuel candidates
      else
        match query with
        | .inl (.inl n) =>
            runResolvedObserve
              (canonicalizeObserve table
                (fun nextContext remaining value =>
                  recursivelyRun value.1 candidates nextContext remaining table value.2))
              context fuel table ((splitUniformImpl n).run cache)
        | .inl (.inr input) =>
            let plan := purePlanProbingHashQuery parameter input context.state
            let nextCandidates := appendPlannedCandidate candidates
              (rootAwarePlannedCandidate? parameter input context.state)
            if hnextSelected : ordinal < nextCandidates.length then
              ordinalRootFinalizationObserve table target rightRoot ordinal context fuel
                nextCandidates
            else
              runResolvedObserve
                (canonicalizeObserve table
                  (fun nextContext remaining value =>
                    recursivelyRun value.1 nextCandidates nextContext remaining table value.2))
                context fuel table ((probingHashQueryAfterPlan parameter input plan).run cache)
        | .inr message =>
            runResolvedObserve
              (canonicalizeObserve table
                (fun nextContext remaining value =>
                  recursivelyRun value.1 candidates nextContext remaining table value.2))
              context fuel table ((maskedSign parameter root ftsSecret message).run cache))
    computation candidates context fuel table cache

set_option maxRecDepth 100000 in
theorem directBoundaryPrivateOrdinalFinalizationRisk_dooms
    (ordinal : Nat) (parameter : PublicParameter) (root : Digest)
    (ftsSecret : Index → FtsTree → FtsLeaf → Digest)
    (target : Position) (rightRoot : Digest)
    (computation : OracleComp (OracleWorld + SigningSpec) α)
    (candidates : List Probe) (context : DeferredContext) (fuel : Nat)
    (table : OtsSecretIndex → HashOutput) (cache : SplitHashCache)
    (hconsistent : context.ValuesConsistent)
    (hstarts : StartTableAgrees context.state table)
    (hdoomed : ¬DeferredCompletable table context) :
    evalDist (directBoundaryPrivateOrdinalFinalizationRisk ordinal parameter root ftsSecret
        target rightRoot computation candidates context fuel table cache) =
      evalDist (pure true : ProbComp Bool) := by
  induction computation using OracleComp.inductionOn generalizing
      candidates context fuel cache with
  | pure value =>
      rw [directBoundaryPrivateOrdinalFinalizationRisk, OracleComp.construct_pure]
      exact ObserverDooms.eq_true
        (table := table)
        (observe := fun context fuel (_value : Unit) =>
          ordinalRootFinalizationObserve table target rightRoot ordinal context fuel candidates)
        context fuel () hconsistent hstarts hdoomed
  | query_bind query next ih =>
      rw [directBoundaryPrivateOrdinalFinalizationRisk, OracleComp.construct_query_bind]
      by_cases hselected : ordinal < candidates.length
      · simp only [hselected, ↓reduceDIte]
        exact ObserverDooms.eq_true
          (table := table)
          (observe := fun context fuel (_value : Unit) =>
            ordinalRootFinalizationObserve table target rightRoot ordinal context fuel candidates)
          context fuel () hconsistent hstarts hdoomed
      · simp only [hselected, ↓reduceDIte]
        cases query with
        | inl worldQuery =>
            cases worldQuery with
            | inl n =>
                let nextObserve : DeferredContext → Nat →
                    (Fin (n + 1) × SplitHashCache) → ProbComp Bool :=
                  fun nextContext remaining value =>
                    directBoundaryPrivateOrdinalFinalizationRisk ordinal parameter root ftsSecret
                      target rightRoot (next value.1) candidates nextContext remaining table value.2
                letI : ObserverDooms table nextObserve := ⟨by
                  intro nextContext remaining value hnextConsistent hnextStarts hnextDoomed
                  exact ih value.1 candidates nextContext remaining value.2 hnextConsistent
                    hnextStarts hnextDoomed⟩
                exact evalDist_runResolvedObserve_eq_true_of_not_completable_auto
                  (observe := canonicalizeObserve table nextObserve) context fuel table
                  ((splitUniformImpl n).run cache) hconsistent hstarts hdoomed
            | inr input =>
                let plan := purePlanProbingHashQuery parameter input context.state
                let nextCandidates := appendPlannedCandidate candidates
                  (rootAwarePlannedCandidate? parameter input context.state)
                by_cases hnextSelected : ordinal < nextCandidates.length
                · have hactual : ordinal <
                      (appendPlannedCandidate candidates
                        (rootAwarePlannedCandidate? parameter input context.state)).length := by
                    simpa [nextCandidates] using hnextSelected
                  simp only [hactual, ↓reduceDIte]
                  exact ObserverDooms.eq_true
                    (table := table)
                    (observe := fun context fuel (_value : Unit) =>
                      ordinalRootFinalizationObserve table target rightRoot ordinal context fuel
                        nextCandidates)
                    context fuel () hconsistent hstarts hdoomed
                · have hactual : ¬ordinal <
                      (appendPlannedCandidate candidates
                        (rootAwarePlannedCandidate? parameter input context.state)).length := by
                    simpa [nextCandidates] using hnextSelected
                  simp only [hactual, ↓reduceDIte]
                  let nextObserve : DeferredContext → Nat →
                      (HashOutput × SplitHashCache) → ProbComp Bool :=
                    fun nextContext remaining value =>
                      directBoundaryPrivateOrdinalFinalizationRisk ordinal parameter root
                        ftsSecret target rightRoot (next value.1) nextCandidates nextContext
                        remaining table value.2
                  letI : ObserverDooms table nextObserve := ⟨by
                    intro nextContext remaining value hnextConsistent hnextStarts hnextDoomed
                    exact ih value.1 nextCandidates nextContext remaining value.2 hnextConsistent
                      hnextStarts hnextDoomed⟩
                  exact evalDist_runResolvedObserve_eq_true_of_not_completable_auto
                    (observe := canonicalizeObserve table nextObserve) context fuel table
                    ((probingHashQueryAfterPlan parameter input plan).run cache)
                    hconsistent hstarts hdoomed
        | inr message =>
            let nextObserve : DeferredContext → Nat →
                (Option Signature × SplitHashCache) → ProbComp Bool :=
              fun nextContext remaining value =>
                directBoundaryPrivateOrdinalFinalizationRisk ordinal parameter root ftsSecret
                  target rightRoot (next value.1) candidates nextContext remaining table value.2
            letI : ObserverDooms table nextObserve := ⟨by
              intro nextContext remaining value hnextConsistent hnextStarts hnextDoomed
              exact ih value.1 candidates nextContext remaining value.2 hnextConsistent
                hnextStarts hnextDoomed⟩
            exact evalDist_runResolvedObserve_eq_true_of_not_completable_auto
              (observe := canonicalizeObserve table nextObserve) context fuel table
              ((maskedSign parameter root ftsSecret message).run cache)
              hconsistent hstarts hdoomed

set_option maxRecDepth 100000 in
set_option maxHeartbeats 4000000 in
theorem directBoundaryPrivateOrdinalFinalizationRisk_synchronized
    (ordinal : Nat) (parameter : PublicParameter) (root : Digest)
    (ftsSecret : Index → FtsTree → FtsLeaf → Digest)
    (target : Position) (rightRoot : Digest)
    (computation : OracleComp (OracleWorld + SigningSpec) α)
    (candidates : List Probe) (left right : DeferredContext) (fuel : Nat)
    (table : OtsSecretIndex → HashOutput) (cache : SplitHashCache)
    (hcontext : FinalizationContextEq table (some left) (some right))
    (hvalues : left.state.values = right.state.values)
    (hrevealed : left.state.revealed = right.state.revealed) :
    evalDist (directBoundaryPrivateOrdinalFinalizationRisk ordinal parameter root ftsSecret
        target rightRoot computation candidates left fuel table cache) =
      evalDist (directBoundaryPrivateOrdinalFinalizationRisk ordinal parameter root ftsSecret
        target rightRoot computation candidates right fuel table cache) := by
  induction computation using OracleComp.inductionOn generalizing
      candidates left right fuel cache with
  | pure value =>
      rw [directBoundaryPrivateOrdinalFinalizationRisk, OracleComp.construct_pure,
        directBoundaryPrivateOrdinalFinalizationRisk, OracleComp.construct_pure]
      exact ObserverSynchronized.eq_of_synchronized
        (table := table)
        (observe := fun context fuel (_value : Unit) =>
          ordinalRootFinalizationObserve table target rightRoot ordinal context fuel candidates)
        left right fuel () hcontext hvalues hrevealed
  | query_bind query next ih =>
      by_cases hselected : ordinal < candidates.length
      · simp only [directBoundaryPrivateOrdinalFinalizationRisk,
          OracleComp.construct_query_bind, hselected, ↓reduceDIte]
        exact ObserverSynchronized.eq_of_synchronized
          (table := table)
          (observe := fun context fuel (_value : Unit) =>
            ordinalRootFinalizationObserve table target rightRoot ordinal context fuel candidates)
          left right fuel () hcontext hvalues hrevealed
      · cases query with
        | inl worldQuery =>
            cases worldQuery with
            | inl n =>
                simp only [directBoundaryPrivateOrdinalFinalizationRisk,
                  OracleComp.construct_query_bind, hselected, ↓reduceDIte]
                let nextObserve : DeferredContext → Nat →
                    (Fin (n + 1) × SplitHashCache) → ProbComp Bool :=
                  fun nextContext remaining value =>
                    directBoundaryPrivateOrdinalFinalizationRisk ordinal parameter root ftsSecret
                      target rightRoot (next value.1) candidates nextContext remaining table value.2
                letI : ObserverDooms table nextObserve := ⟨by
                  intro nextContext remaining value hnextConsistent hnextStarts hnextDoomed
                  exact directBoundaryPrivateOrdinalFinalizationRisk_dooms ordinal parameter root
                    ftsSecret target rightRoot (next value.1) candidates nextContext remaining table
                    value.2 hnextConsistent hnextStarts hnextDoomed⟩
                letI : ObserverSynchronized table nextObserve := ⟨by
                  intro nextLeft nextRight remaining value hnextContext hnextValues hnextRevealed
                  exact ih value.1 candidates nextLeft nextRight remaining value.2 hnextContext
                    hnextValues hnextRevealed⟩
                exact evalDist_runResolvedObserve_eq_of_finalizationSynchronized
                  (observe := canonicalizeObserve table nextObserve)
                  ((splitUniformImpl n).run cache) left right fuel table hcontext hvalues hrevealed
            | inr input =>
                have hplan : purePlanProbingHashQuery parameter input left.state =
                    purePlanProbingHashQuery parameter input right.state :=
                  purePlanProbingHashQuery_eq_of_values_eq hvalues parameter input
                have hcandidate : rootAwarePlannedCandidate? parameter input left.state =
                    rootAwarePlannedCandidate? parameter input right.state := by
                  unfold rootAwarePlannedCandidate?
                  rw [hplan]
                let nextCandidates := appendPlannedCandidate candidates
                  (rootAwarePlannedCandidate? parameter input left.state)
                simp only [directBoundaryPrivateOrdinalFinalizationRisk,
                  OracleComp.construct_query_bind, hselected, ↓reduceDIte, ← hplan, ← hcandidate]
                by_cases hnextSelected : ordinal < nextCandidates.length
                · have hactual : ordinal <
                      (appendPlannedCandidate candidates
                        (rootAwarePlannedCandidate? parameter input left.state)).length := by
                    simpa [nextCandidates] using hnextSelected
                  simp only [hactual, ↓reduceDIte]
                  exact ObserverSynchronized.eq_of_synchronized
                    (table := table)
                    (observe := fun context fuel (_value : Unit) =>
                      ordinalRootFinalizationObserve table target rightRoot ordinal context fuel
                        nextCandidates)
                    left right fuel () hcontext hvalues hrevealed
                · have hactual : ¬ordinal <
                      (appendPlannedCandidate candidates
                        (rootAwarePlannedCandidate? parameter input left.state)).length := by
                    simpa [nextCandidates] using hnextSelected
                  simp only [hactual, ↓reduceDIte]
                  let nextObserve : DeferredContext → Nat →
                      (HashOutput × SplitHashCache) → ProbComp Bool :=
                    fun nextContext remaining value =>
                      directBoundaryPrivateOrdinalFinalizationRisk ordinal parameter root
                        ftsSecret target rightRoot (next value.1) nextCandidates nextContext
                        remaining table value.2
                  letI : ObserverDooms table nextObserve := ⟨by
                    intro nextContext remaining value hnextConsistent hnextStarts hnextDoomed
                    exact directBoundaryPrivateOrdinalFinalizationRisk_dooms ordinal parameter root
                      ftsSecret target rightRoot (next value.1) nextCandidates nextContext remaining
                      table value.2 hnextConsistent hnextStarts hnextDoomed⟩
                  letI : ObserverSynchronized table nextObserve := ⟨by
                    intro nextLeft nextRight remaining value hnextContext hnextValues hnextRevealed
                    exact ih value.1 nextCandidates nextLeft nextRight remaining value.2
                      hnextContext hnextValues hnextRevealed⟩
                  exact evalDist_runResolvedObserve_eq_of_finalizationSynchronized
                    (observe := canonicalizeObserve table nextObserve)
                    ((probingHashQueryAfterPlan parameter input
                      (purePlanProbingHashQuery parameter input left.state)).run cache)
                    left right fuel table hcontext hvalues hrevealed
        | inr message =>
            simp only [directBoundaryPrivateOrdinalFinalizationRisk,
              OracleComp.construct_query_bind, hselected, ↓reduceDIte]
            let nextObserve : DeferredContext → Nat →
                (Option Signature × SplitHashCache) → ProbComp Bool :=
              fun nextContext remaining value =>
                directBoundaryPrivateOrdinalFinalizationRisk ordinal parameter root ftsSecret
                  target rightRoot (next value.1) candidates nextContext remaining table value.2
            letI : ObserverDooms table nextObserve := ⟨by
              intro nextContext remaining value hnextConsistent hnextStarts hnextDoomed
              exact directBoundaryPrivateOrdinalFinalizationRisk_dooms ordinal parameter root
                ftsSecret target rightRoot (next value.1) candidates nextContext remaining table
                value.2 hnextConsistent hnextStarts hnextDoomed⟩
            letI : ObserverSynchronized table nextObserve := ⟨by
              intro nextLeft nextRight remaining value hnextContext hnextValues hnextRevealed
              exact ih value.1 candidates nextLeft nextRight remaining value.2 hnextContext
                hnextValues hnextRevealed⟩
            exact evalDist_runResolvedObserve_eq_of_finalizationSynchronized
              (observe := canonicalizeObserve table nextObserve)
              ((maskedSign parameter root ftsSecret message).run cache)
              left right fuel table hcontext hvalues hrevealed

set_option maxRecDepth 100000 in
set_option maxHeartbeats 4000000 in
theorem evalDist_resolveDeferredPositionValue_then_directBoundaryPrivateOrdinalFinalizationRisk
    (ordinal : Nat) (parameter : PublicParameter) (root : Digest)
    (ftsSecret : Index → FtsTree → FtsLeaf → Digest)
    (target : Position) (rightRoot : Digest)
    (position : Position)
    (computation : OracleComp (OracleWorld + SigningSpec) α)
    (candidates : List Probe) (context : DeferredContext) (fuel : Nat)
    (table : OtsSecretIndex → HashOutput) (cache : SplitHashCache)
    (hvalid : context.Valid) (hcompletable : DeferredCompletable table context)
    (hensured : Coordinate.position position ∈ context.state.ensured) :
    evalDist (resolveDeferredPositionValue position context >>= fun resolved =>
      match resolved with
      | none => pure true
      | some resolved =>
          directBoundaryPrivateOrdinalFinalizationRisk ordinal parameter root ftsSecret target
            rightRoot computation candidates resolved.toDeferredContext fuel table cache) =
      evalDist (directBoundaryPrivateOrdinalFinalizationRisk ordinal parameter root ftsSecret
        target rightRoot computation candidates context fuel table cache) := by
  induction computation using OracleComp.inductionOn generalizing
      candidates context fuel cache position with
  | pure value =>
      rw [directBoundaryPrivateOrdinalFinalizationRisk, OracleComp.construct_pure]
      exact ObserverPositionNeutral.eq_resolve
        (table := table)
        (observe := fun context fuel (_value : Unit) =>
          ordinalRootFinalizationObserve table target rightRoot ordinal context fuel candidates)
        position context fuel () hvalid hcompletable hensured
  | query_bind query next ih =>
      by_cases hselected : ordinal < candidates.length
      · simp only [directBoundaryPrivateOrdinalFinalizationRisk,
          OracleComp.construct_query_bind, hselected, ↓reduceDIte]
        exact ObserverPositionNeutral.eq_resolve
          (table := table)
          (observe := fun context fuel (_value : Unit) =>
            ordinalRootFinalizationObserve table target rightRoot ordinal context fuel candidates)
          position context fuel () hvalid hcompletable hensured
      · cases query with
        | inl worldQuery =>
            cases worldQuery with
            | inl n =>
                simp only [directBoundaryPrivateOrdinalFinalizationRisk,
                  OracleComp.construct_query_bind, hselected, ↓reduceDIte]
                let nextObserve : DeferredContext → Nat →
                    (Fin (n + 1) × SplitHashCache) → ProbComp Bool :=
                  fun nextContext remaining value =>
                    directBoundaryPrivateOrdinalFinalizationRisk ordinal parameter root ftsSecret
                      target rightRoot (next value.1) candidates nextContext remaining table value.2
                letI : ObserverDooms table nextObserve := ⟨by
                  intro nextContext remaining value hnextConsistent hnextStarts hnextDoomed
                  exact directBoundaryPrivateOrdinalFinalizationRisk_dooms ordinal parameter root
                    ftsSecret target rightRoot (next value.1) candidates nextContext remaining table
                    value.2 hnextConsistent hnextStarts hnextDoomed⟩
                letI : ObserverPositionNeutral table nextObserve := ⟨by
                  intro position nextContext remaining value hnextValid hnextCompletable
                    hnextEnsured
                  exact ih value.1 position candidates nextContext remaining value.2 hnextValid
                    hnextCompletable hnextEnsured⟩
                have hmove :=
                  evalDist_resolveDeferredPositionValue_then_runResolvedObserve_auto position
                    (observe := canonicalizeObserve table nextObserve)
                    ((splitUniformImpl n).run cache) context fuel table hvalid hcompletable hensured
                exact hmove
            | inr input =>
                let plan := purePlanProbingHashQuery parameter input context.state
                let nextCandidates := appendPlannedCandidate candidates
                  (rootAwarePlannedCandidate? parameter input context.state)
                let nextObserve : DeferredContext → Nat →
                    (HashOutput × SplitHashCache) → ProbComp Bool :=
                  fun nextContext remaining value =>
                    directBoundaryPrivateOrdinalFinalizationRisk ordinal parameter root ftsSecret
                      target rightRoot (next value.1) nextCandidates nextContext remaining table
                      value.2
                have hnormalize : evalDist (resolveDeferredPositionValue position context >>=
                    fun resolved => match resolved with
                    | none => pure true
                    | some resolved =>
                        if hnextSelected : ordinal < nextCandidates.length then
                          ordinalRootFinalizationObserve table target rightRoot ordinal
                            resolved.toDeferredContext fuel nextCandidates
                        else runResolvedObserve (canonicalizeObserve table nextObserve)
                          resolved.toDeferredContext fuel table
                          ((probingHashQueryAfterPlan parameter input plan).run cache)) =
                    evalDist (resolveDeferredPositionValue position context >>= fun resolved =>
                      match resolved with
                      | none => pure true
                      | some resolved =>
                          directBoundaryPrivateOrdinalFinalizationRisk ordinal parameter root
                            ftsSecret target rightRoot
                            (liftM (OracleSpec.query (Sum.inl (Sum.inr input))) >>= next)
                            candidates resolved.toDeferredContext fuel table cache) := by
                  apply evalDist_bind_congr
                  intro resolved hresolved
                  cases resolved with
                  | none => rfl
                  | some resolved =>
                      have hvalues := resolveDeferredPositionValue_preserves_state_values position
                        context resolved hresolved
                      have hplan : purePlanProbingHashQuery parameter input resolved.state = plan := by
                        simpa [plan] using
                          (purePlanProbingHashQuery_eq_of_values_eq hvalues parameter input)
                      have hcandidate :
                          rootAwarePlannedCandidate? parameter input resolved.state =
                            rootAwarePlannedCandidate? parameter input context.state := by
                        unfold rootAwarePlannedCandidate?
                        rw [hplan]
                      simp only [directBoundaryPrivateOrdinalFinalizationRisk,
                        OracleComp.construct_query_bind, hselected, ↓reduceDIte, hplan, hcandidate]
                      rfl
                rw [← hnormalize]
                rw [directBoundaryPrivateOrdinalFinalizationRisk,
                  OracleComp.construct_query_bind]
                simp only [hselected, ↓reduceDIte]
                by_cases hnextSelected : ordinal < nextCandidates.length
                · have hactual : ordinal <
                      (appendPlannedCandidate candidates
                        (rootAwarePlannedCandidate? parameter input context.state)).length := by
                    simpa [nextCandidates] using hnextSelected
                  simp only [hnextSelected, hactual, ↓reduceDIte]
                  have hneutral := ObserverPositionNeutral.eq_resolve
                    (table := table)
                    (observe := fun context fuel (_value : Unit) =>
                      ordinalRootFinalizationObserve table target rightRoot ordinal context fuel
                        nextCandidates)
                    position context fuel () hvalid hcompletable hensured
                  exact hneutral
                · have hactual : ¬ordinal <
                      (appendPlannedCandidate candidates
                        (rootAwarePlannedCandidate? parameter input context.state)).length := by
                    simpa [nextCandidates] using hnextSelected
                  simp only [hnextSelected, hactual, ↓reduceDIte]
                  letI : ObserverDooms table nextObserve := ⟨by
                    intro nextContext remaining value hnextConsistent hnextStarts hnextDoomed
                    exact directBoundaryPrivateOrdinalFinalizationRisk_dooms ordinal parameter root
                      ftsSecret target rightRoot (next value.1) nextCandidates nextContext remaining
                      table value.2 hnextConsistent hnextStarts hnextDoomed⟩
                  letI : ObserverPositionNeutral table nextObserve := ⟨by
                    intro nextPosition nextContext remaining value hnextValid hnextCompletable
                      hnextEnsured
                    exact ih value.1 nextPosition nextCandidates nextContext remaining value.2
                      hnextValid hnextCompletable hnextEnsured⟩
                  have hmove :=
                    evalDist_resolveDeferredPositionValue_then_runResolvedObserve_auto position
                      (observe := canonicalizeObserve table nextObserve)
                      ((probingHashQueryAfterPlan parameter input plan).run cache) context fuel table
                      hvalid hcompletable hensured
                  exact hmove
        | inr message =>
            simp only [directBoundaryPrivateOrdinalFinalizationRisk,
              OracleComp.construct_query_bind, hselected, ↓reduceDIte]
            let nextObserve : DeferredContext → Nat →
                (Option Signature × SplitHashCache) → ProbComp Bool :=
              fun nextContext remaining value =>
                directBoundaryPrivateOrdinalFinalizationRisk ordinal parameter root ftsSecret
                  target rightRoot (next value.1) candidates nextContext remaining table value.2
            letI : ObserverDooms table nextObserve := ⟨by
              intro nextContext remaining value hnextConsistent hnextStarts hnextDoomed
              exact directBoundaryPrivateOrdinalFinalizationRisk_dooms ordinal parameter root
                ftsSecret target rightRoot (next value.1) candidates nextContext remaining table
                value.2 hnextConsistent hnextStarts hnextDoomed⟩
            letI : ObserverPositionNeutral table nextObserve := ⟨by
              intro position nextContext remaining value hnextValid hnextCompletable hnextEnsured
              exact ih value.1 position candidates nextContext remaining value.2 hnextValid
                hnextCompletable hnextEnsured⟩
            have hmove :=
              evalDist_resolveDeferredPositionValue_then_runResolvedObserve_auto position
                (observe := canonicalizeObserve table nextObserve)
                ((maskedSign parameter root ftsSecret message).run cache) context fuel table hvalid
                hcompletable hensured
            exact hmove

def PrivateOrdinalRootRiskRel
    (target : Position) (rightRoot : Digest) (ordinal : Nat)
    (selection : Option PrivateOrdinalSelection) (hit : Bool) : Prop :=
  privateOrdinalSelectionGoodForSomeOutput target rightRoot ordinal selection → hit = true

theorem relTriple_pureSelection_rootRisk
    (target : Position) (rightRoot : Digest) (ordinal : Nat)
    (selection : Option PrivateOrdinalSelection) (risk : ProbComp Bool)
    (hfire : privateOrdinalSelectionGoodForSomeOutput target rightRoot ordinal selection →
      evalDist risk = evalDist (pure true : ProbComp Bool)) :
    RelTriple (pure selection : ProbComp (Option PrivateOrdinalSelection)) risk
      (PrivateOrdinalRootRiskRel target rightRoot ordinal) := by
  by_cases hgood :
      privateOrdinalSelectionGoodForSomeOutput target rightRoot ordinal selection
  · have hbase := relTriple_true
      (pure selection : ProbComp (Option PrivateOrdinalSelection))
      (pure true : ProbComp Bool)
    have hsupport :=
      SphincsSecurity.Concrete.FtsProbeSimulation.relTriple_and_right_support hbase
    have hrel : RelTriple
        (pure selection : ProbComp (Option PrivateOrdinalSelection))
        (pure true : ProbComp Bool)
        (PrivateOrdinalRootRiskRel target rightRoot ordinal) := by
      apply relTriple_post_mono hsupport
      intro _left right hrelation _hleft
      simpa using hrelation.2
    exact relTriple_of_evalDist_eq_right (hfire hgood).symm hrel
  · apply relTriple_post_mono
      (SphincsSecurity.Concrete.FtsProbeSimulation.relTriple_and_left_support
        (relTriple_true (pure selection : ProbComp (Option PrivateOrdinalSelection)) risk)
        (fun left => left = selection) (by intro left hleft; simpa using hleft))
    intro left _right hrelation hleft
    exact False.elim (hgood (hrelation.2 ▸ hleft))

theorem relTriple_selected_ordinalRootFinalizationObserve
    (table : OtsSecretIndex → HashOutput)
    (target : Position) (rightRoot : Digest) (ordinal : Nat)
    (context : DeferredContext) (fuel : Nat) (candidates : List Probe)
    (hselected : ordinal < candidates.length)
    (hvalid : context.Valid) (hcompletable : DeferredCompletable table context) :
    RelTriple
      (pure (some ⟨candidates.get ⟨ordinal, hselected⟩, context, candidates⟩) :
        ProbComp (Option PrivateOrdinalSelection))
      (ordinalRootFinalizationObserve table target rightRoot ordinal context fuel candidates)
      (PrivateOrdinalRootRiskRel target rightRoot ordinal) := by
  apply relTriple_pureSelection_rootRisk
  rintro ⟨output, hgood⟩
  have hright : CandidatesAvoidRoot target rightRoot (candidates.take ordinal) := by
    intro candidate hcandidate
    exact (hgood.2.2.2.2 candidate hcandidate).2
  have hcoordinate :
      (candidates.get ⟨ordinal, hselected⟩).coordinate = .position target := by
    simpa using congrArg Probe.coordinate hgood.1
  unfold ordinalRootFinalizationObserve
  simp only [hselected, ↓reduceDIte, hcoordinate, hright, and_self, if_true]
  exact evalDist_candidateFinalizationObserve_eq_true_of_goodForRoots table
    ⟨candidates.get ⟨ordinal, hselected⟩, context, candidates⟩ fuel target output
    rightRoot ordinal hvalid hcompletable hgood

set_option maxRecDepth 100000 in
theorem relTriple_runWitnessSelection_runResolvedObserve
    (table : OtsSecretIndex → HashOutput)
    (target : Position) (rightRoot : Digest) (ordinal : Nat)
    (selectionObserve : DeferredContext → Nat → α → List Probe →
      ProbComp (Option PrivateOrdinalSelection))
    (riskObserve : DeferredContext → Nat → α → ProbComp Bool)
    [ObserverDooms table riskObserve] [ObserverSynchronized table riskObserve]
    [ObserverPositionNeutral table riskObserve]
    (candidates : List Probe) (context : DeferredContext) (fuel : Nat)
    (computation : OracleComp (LazyRevealProbe.World Coordinate) α)
    (hvalid : context.Valid) (hcompletable : DeferredCompletable table context)
    (hobserve : ∀ result,
      DirectDetailedResult.done result ∈ support
          (runDirectResolvedDetailedFromTable context fuel table computation) →
        RelTriple
          (selectionObserve result.context result.remaining result.value candidates)
          (riskObserve result.context result.remaining result.value)
          (PrivateOrdinalRootRiskRel target rightRoot ordinal)) :
    RelTriple
      (runDirectResolvedWitnessFromTable context fuel table computation >>=
        finishDirectPrivateOrdinalSelection selectionObserve candidates)
      (runResolvedObserve riskObserve context fuel table computation)
      (PrivateOrdinalRootRiskRel target rightRoot ordinal) := by
  apply relTriple_of_evalDist_eq_left
    (evalDist_runWitnessSelection_eq_detailed selectionObserve candidates context fuel table
      computation)
  apply relTriple_of_evalDist_eq_right
    (evalDist_runResolvedObserve_eq_runDirectResolvedObserve riskObserve context fuel table
      computation hvalid hcompletable).symm
  unfold runDirectResolvedObserve
  rw [← map_toOption_runDirectResolvedDetailedFromTable computation context fuel table,
    map_eq_bind_pure_comp, bind_assoc]
  let run := runDirectResolvedDetailedFromTable context fuel table computation
  have hrun :=
    SphincsSecurity.Concrete.FtsProbeSimulation.relTriple_and_left_support
      (relTriple_refl run) (fun result => result ∈ support run)
      (fun result hresult => hresult)
  apply relTriple_bind hrun
  intro leftResult rightResult hrelation
  rcases hrelation with ⟨heq, hleftMem⟩
  subst rightResult
  cases leftResult with
  | stopped reason =>
      simp only [finishDirectDetailedPrivateOrdinalSelection, Function.comp_apply, pure_bind,
        DirectDetailedResult.toOption, finishObserve]
      apply relTriple_pureSelection_rootRisk
      simp [privateOrdinalSelectionGoodForSomeOutput]
  | done result =>
      simpa [finishDirectDetailedPrivateOrdinalSelection, Function.comp_apply,
        DirectDetailedResult.toOption, finishObserve] using hobserve result hleftMem

theorem relTriple_canonicalSelection_canonicalObserve
    (table : OtsSecretIndex → HashOutput)
    (target : Position) (rightRoot : Digest) (ordinal : Nat)
    (selectionObserve : DeferredContext → Nat → α → List Probe →
      ProbComp (Option PrivateOrdinalSelection))
    (riskObserve : DeferredContext → Nat → α → ProbComp Bool)
    (context : DeferredContext) (fuel : Nat) (value : α) (candidates : List Probe)
    (hrecursive : PublishedValues context.state →
      DeferredCompletable table (canonicalizeMaterializedValues table context) →
      RelTriple
        (selectionObserve (canonicalizeMaterializedValues table context) fuel value candidates)
        (riskObserve (canonicalizeMaterializedValues table context) fuel value)
        (PrivateOrdinalRootRiskRel target rightRoot ordinal)) :
    RelTriple
      (canonicalizeDirectPrivateOrdinalSelection table selectionObserve context fuel value
        candidates)
      (canonicalizeObserve table riskObserve context fuel value)
      (PrivateOrdinalRootRiskRel target rightRoot ordinal) := by
  classical
  unfold canonicalizeDirectPrivateOrdinalSelection canonicalizeObserve
  let canonical := canonicalizeMaterializedValues table context
  by_cases hhit : PrivateStructuralHit canonical
  · simp only [canonical, hhit]
    by_cases hpublished : PublishedValues context.state
    · simp only [hpublished, ↓reduceIte]
      apply relTriple_pureSelection_rootRisk
      simp [privateOrdinalSelectionGoodForSomeOutput]
    · simp only [hpublished, ↓reduceIte]
      apply relTriple_pureSelection_rootRisk
      simp [privateOrdinalSelectionGoodForSomeOutput]
  · simp only [canonical, hhit]
    by_cases hpublished : PublishedValues context.state
    · simp only [hpublished, ↓reduceIte]
      by_cases hcompletable : DeferredCompletable table canonical
      · simpa [canonical, hcompletable] using hrecursive hpublished hcompletable
      · simp only [canonical, hcompletable, ↓reduceIte]
        apply relTriple_pureSelection_rootRisk
        simp [privateOrdinalSelectionGoodForSomeOutput]
    · simp only [hpublished, ↓reduceIte]
      apply relTriple_pureSelection_rootRisk
      simp [privateOrdinalSelectionGoodForSomeOutput]

theorem resolvedCore_of_done_runDirectResolvedDetailedFromTable
    (computation : OracleComp (LazyRevealProbe.World Coordinate) α)
    (context : DeferredContext) (fuel : Nat)
    (table : OtsSecretIndex → HashOutput) (result : ResolvedRunResult α)
    (hconsistent : context.ValuesConsistent)
    (hstarts : StartTableAgrees context.state table)
    (hresult : DirectDetailedResult.done result ∈ support
      (runDirectResolvedDetailedFromTable context fuel table computation)) :
    result.table = table ∧ result.context.ValuesConsistent ∧
      StartTableAgrees result.context.state table := by
  apply resolvedCore_of_mem_runDirectResolvedFromTable computation context fuel table result
    hconsistent hstarts
  rw [← map_toOption_runDirectResolvedDetailedFromTable computation context fuel table,
    support_map]
  exact ⟨.done result, hresult, rfl⟩

set_option maxRecDepth 100000 in
set_option maxHeartbeats 4000000 in
theorem relTriple_directBoundaryPrivateOrdinalSelection_finalizationRisk
    (ordinal : Nat) (parameter : PublicParameter) (root : Digest)
    (ftsSecret : Index → FtsTree → FtsLeaf → Digest)
    (target : Position) (rightRoot : Digest)
    (computation : OracleComp (OracleWorld + SigningSpec) α)
    (candidates : List Probe) (context : DeferredContext) (fuel : Nat)
    (table : OtsSecretIndex → HashOutput) (cache : SplitHashCache)
    (hvalid : context.Valid) (hcompletable : DeferredCompletable table context) :
    RelTriple
      (directDetailedBoundaryPrivateOrdinalSelection ordinal parameter root ftsSecret computation
        candidates context fuel table cache)
      (directBoundaryPrivateOrdinalFinalizationRisk ordinal parameter root ftsSecret target
        rightRoot computation candidates context fuel table cache)
      (PrivateOrdinalRootRiskRel target rightRoot ordinal) := by
  induction computation using OracleComp.inductionOn generalizing
      candidates context fuel cache with
  | pure value =>
      rw [directDetailedBoundaryPrivateOrdinalSelection, OracleComp.construct_pure,
        directBoundaryPrivateOrdinalFinalizationRisk, OracleComp.construct_pure]
      by_cases hselected : ordinal < candidates.length
      · simp only [selectedPrivateOrdinal?, hselected, ↓reduceDIte]
        exact relTriple_selected_ordinalRootFinalizationObserve table target rightRoot ordinal
          context fuel candidates hselected hvalid hcompletable
      · simp only [selectedPrivateOrdinal?, hselected, ↓reduceDIte]
        apply relTriple_pureSelection_rootRisk
        simp [privateOrdinalSelectionGoodForSomeOutput]
  | query_bind query next ih =>
      rw [directDetailedBoundaryPrivateOrdinalSelection, OracleComp.construct_query_bind,
        directBoundaryPrivateOrdinalFinalizationRisk, OracleComp.construct_query_bind]
      by_cases hselected : ordinal < candidates.length
      · simp only [hselected, ↓reduceDIte]
        exact relTriple_selected_ordinalRootFinalizationObserve table target rightRoot ordinal
          context fuel candidates hselected hvalid hcompletable
      · simp only [hselected, ↓reduceDIte]
        cases query with
        | inl worldQuery =>
            cases worldQuery with
            | inl n =>
                let nextSelection : DeferredContext → Nat →
                    (Fin (n + 1) × SplitHashCache) → List Probe →
                      ProbComp (Option PrivateOrdinalSelection) :=
                  fun nextContext remaining value laterCandidates =>
                    directDetailedBoundaryPrivateOrdinalSelection ordinal parameter root ftsSecret
                      (next value.1) laterCandidates nextContext remaining table value.2
                let nextRisk : DeferredContext → Nat →
                    (Fin (n + 1) × SplitHashCache) → ProbComp Bool :=
                  fun nextContext remaining value =>
                    directBoundaryPrivateOrdinalFinalizationRisk ordinal parameter root ftsSecret
                      target rightRoot (next value.1) candidates nextContext remaining table value.2
                letI : ObserverDooms table nextRisk := ⟨by
                  intro nextContext remaining value hconsistent hstarts hdoomed
                  exact directBoundaryPrivateOrdinalFinalizationRisk_dooms ordinal parameter root
                    ftsSecret target rightRoot (next value.1) candidates nextContext remaining table
                    value.2 hconsistent hstarts hdoomed⟩
                letI : ObserverSynchronized table nextRisk := ⟨by
                  intro left right remaining value hcontext hvalues hrevealed
                  exact directBoundaryPrivateOrdinalFinalizationRisk_synchronized ordinal
                    parameter root ftsSecret target rightRoot (next value.1) candidates left right
                    remaining table value.2 hcontext hvalues hrevealed⟩
                letI : ObserverPositionNeutral table nextRisk := ⟨by
                  intro position nextContext remaining value hnextValid hnextCompletable hensured
                  exact evalDist_resolveDeferredPositionValue_then_directBoundaryPrivateOrdinalFinalizationRisk
                    ordinal parameter root ftsSecret target rightRoot position (next value.1)
                    candidates nextContext remaining table value.2 hnextValid hnextCompletable
                    hensured⟩
                apply relTriple_runWitnessSelection_runResolvedObserve table target rightRoot ordinal
                  (canonicalizeDirectPrivateOrdinalSelection table nextSelection)
                  (canonicalizeObserve table nextRisk) candidates context fuel
                  ((splitUniformImpl n).run cache) hvalid hcompletable
                intro result hresult
                have hcore := resolvedCore_of_done_runDirectResolvedDetailedFromTable
                  ((splitUniformImpl n).run cache) context fuel table result
                  hvalid.valuesConsistent (startTableAgrees_of_deferredCompletable hcompletable)
                  hresult
                apply relTriple_canonicalSelection_canonicalObserve table target rightRoot ordinal
                  nextSelection nextRisk result.context result.remaining result.value candidates
                intro _hpublished hcanonicalCompletable
                have hcanonicalConsistent := canonicalizeMaterializedValues_valuesConsistent table
                  result.context hcore.2.1
                have hcanonicalStarts := canonicalizeMaterializedValues_startTableAgrees table
                  result.context
                have hcanonicalValid := valid_of_resolvedCore_completable table
                  (canonicalizeMaterializedValues table result.context) hcanonicalConsistent
                  hcanonicalStarts hcanonicalCompletable
                simpa [nextSelection, nextRisk] using
                  (ih result.value.1 candidates
                    (canonicalizeMaterializedValues table result.context) result.remaining
                    result.value.2 hcanonicalValid hcanonicalCompletable)
            | inr input =>
                let plan := purePlanProbingHashQuery parameter input context.state
                let nextCandidates := appendPlannedCandidate candidates
                  (rootAwarePlannedCandidate? parameter input context.state)
                by_cases hnextSelected : ordinal < nextCandidates.length
                · have hactual : ordinal <
                      (appendPlannedCandidate candidates
                        (rootAwarePlannedCandidate? parameter input context.state)).length := by
                    simpa [nextCandidates] using hnextSelected
                  simp only [hactual, ↓reduceDIte]
                  exact relTriple_selected_ordinalRootFinalizationObserve table target rightRoot
                    ordinal context fuel nextCandidates hnextSelected hvalid hcompletable
                · have hactual : ¬ordinal <
                      (appendPlannedCandidate candidates
                        (rootAwarePlannedCandidate? parameter input context.state)).length := by
                    simpa [nextCandidates] using hnextSelected
                  simp only [hactual, ↓reduceDIte]
                  let nextSelection : DeferredContext → Nat →
                      (HashOutput × SplitHashCache) → List Probe →
                        ProbComp (Option PrivateOrdinalSelection) :=
                    fun nextContext remaining value laterCandidates =>
                      directDetailedBoundaryPrivateOrdinalSelection ordinal parameter root
                        ftsSecret (next value.1) laterCandidates nextContext remaining table value.2
                  let nextRisk : DeferredContext → Nat →
                      (HashOutput × SplitHashCache) → ProbComp Bool :=
                    fun nextContext remaining value =>
                      directBoundaryPrivateOrdinalFinalizationRisk ordinal parameter root ftsSecret
                        target rightRoot (next value.1) nextCandidates nextContext remaining table
                        value.2
                  letI : ObserverDooms table nextRisk := ⟨by
                    intro nextContext remaining value hconsistent hstarts hdoomed
                    exact directBoundaryPrivateOrdinalFinalizationRisk_dooms ordinal parameter root
                      ftsSecret target rightRoot (next value.1) nextCandidates nextContext remaining
                      table value.2 hconsistent hstarts hdoomed⟩
                  letI : ObserverSynchronized table nextRisk := ⟨by
                    intro left right remaining value hcontext hvalues hrevealed
                    exact directBoundaryPrivateOrdinalFinalizationRisk_synchronized ordinal
                      parameter root ftsSecret target rightRoot (next value.1) nextCandidates left
                      right remaining table value.2 hcontext hvalues hrevealed⟩
                  letI : ObserverPositionNeutral table nextRisk := ⟨by
                    intro position nextContext remaining value hnextValid hnextCompletable hensured
                    exact evalDist_resolveDeferredPositionValue_then_directBoundaryPrivateOrdinalFinalizationRisk
                      ordinal parameter root ftsSecret target rightRoot position (next value.1)
                      nextCandidates nextContext remaining table value.2 hnextValid
                      hnextCompletable hensured⟩
                  apply relTriple_runWitnessSelection_runResolvedObserve table target rightRoot
                    ordinal (canonicalizeDirectPrivateOrdinalSelection table nextSelection)
                    (canonicalizeObserve table nextRisk) nextCandidates context fuel
                    ((probingHashQueryAfterPlan parameter input plan).run cache) hvalid hcompletable
                  intro result hresult
                  have hcore := resolvedCore_of_done_runDirectResolvedDetailedFromTable
                    ((probingHashQueryAfterPlan parameter input plan).run cache) context fuel table
                    result hvalid.valuesConsistent
                    (startTableAgrees_of_deferredCompletable hcompletable) hresult
                  apply relTriple_canonicalSelection_canonicalObserve table target rightRoot ordinal
                    nextSelection nextRisk result.context result.remaining result.value
                    nextCandidates
                  intro _hpublished hcanonicalCompletable
                  have hcanonicalConsistent :=
                    canonicalizeMaterializedValues_valuesConsistent table result.context hcore.2.1
                  have hcanonicalStarts := canonicalizeMaterializedValues_startTableAgrees table
                    result.context
                  have hcanonicalValid := valid_of_resolvedCore_completable table
                    (canonicalizeMaterializedValues table result.context) hcanonicalConsistent
                    hcanonicalStarts hcanonicalCompletable
                  simpa [nextSelection, nextRisk] using
                    (ih result.value.1 nextCandidates
                      (canonicalizeMaterializedValues table result.context) result.remaining
                      result.value.2 hcanonicalValid hcanonicalCompletable)
        | inr message =>
            let nextSelection : DeferredContext → Nat →
                (Option Signature × SplitHashCache) → List Probe →
                  ProbComp (Option PrivateOrdinalSelection) :=
              fun nextContext remaining value laterCandidates =>
                directDetailedBoundaryPrivateOrdinalSelection ordinal parameter root ftsSecret
                  (next value.1) laterCandidates nextContext remaining table value.2
            let nextRisk : DeferredContext → Nat →
                (Option Signature × SplitHashCache) → ProbComp Bool :=
              fun nextContext remaining value =>
                directBoundaryPrivateOrdinalFinalizationRisk ordinal parameter root ftsSecret
                  target rightRoot (next value.1) candidates nextContext remaining table value.2
            letI : ObserverDooms table nextRisk := ⟨by
              intro nextContext remaining value hconsistent hstarts hdoomed
              exact directBoundaryPrivateOrdinalFinalizationRisk_dooms ordinal parameter root
                ftsSecret target rightRoot (next value.1) candidates nextContext remaining table
                value.2 hconsistent hstarts hdoomed⟩
            letI : ObserverSynchronized table nextRisk := ⟨by
              intro left right remaining value hcontext hvalues hrevealed
              exact directBoundaryPrivateOrdinalFinalizationRisk_synchronized ordinal parameter
                root ftsSecret target rightRoot (next value.1) candidates left right remaining table
                value.2 hcontext hvalues hrevealed⟩
            letI : ObserverPositionNeutral table nextRisk := ⟨by
              intro position nextContext remaining value hnextValid hnextCompletable hensured
              exact evalDist_resolveDeferredPositionValue_then_directBoundaryPrivateOrdinalFinalizationRisk
                ordinal parameter root ftsSecret target rightRoot position (next value.1) candidates
                nextContext remaining table value.2 hnextValid hnextCompletable hensured⟩
            apply relTriple_runWitnessSelection_runResolvedObserve table target rightRoot ordinal
              (canonicalizeDirectPrivateOrdinalSelection table nextSelection)
              (canonicalizeObserve table nextRisk) candidates context fuel
              ((maskedSign parameter root ftsSecret message).run cache) hvalid hcompletable
            intro result hresult
            have hcore := resolvedCore_of_done_runDirectResolvedDetailedFromTable
              ((maskedSign parameter root ftsSecret message).run cache) context fuel table result
              hvalid.valuesConsistent (startTableAgrees_of_deferredCompletable hcompletable)
              hresult
            apply relTriple_canonicalSelection_canonicalObserve table target rightRoot ordinal
              nextSelection nextRisk result.context result.remaining result.value candidates
            intro _hpublished hcanonicalCompletable
            have hcanonicalConsistent := canonicalizeMaterializedValues_valuesConsistent table
              result.context hcore.2.1
            have hcanonicalStarts := canonicalizeMaterializedValues_startTableAgrees table
              result.context
            have hcanonicalValid := valid_of_resolvedCore_completable table
              (canonicalizeMaterializedValues table result.context) hcanonicalConsistent
              hcanonicalStarts hcanonicalCompletable
            simpa [nextSelection, nextRisk] using
              (ih result.value.1 candidates
                (canonicalizeMaterializedValues table result.context) result.remaining
                result.value.2 hcanonicalValid hcanonicalCompletable)

noncomputable def granularPrivateOrdinalFinalizationObserve
    (ordinal : Nat) (adversary : Adversary) (parameter : PublicParameter)
    (table : OtsSecretIndex → HashOutput)
    (ftsSecret : Index → FtsTree → FtsLeaf → Digest)
    (target : Position) (rightRoot : Digest)
    (context : DeferredContext) (fuel : Nat)
    (value : Digest × SplitHashCache) : ProbComp Bool :=
  directBoundaryPrivateOrdinalFinalizationRisk ordinal parameter value.1 ftsSecret target
    rightRoot (retainedGameRestComputation adversary ⟨value.1, parameter⟩) [] context fuel
    table value.2

noncomputable def granularPrivateOrdinalSelectionObserve
    (ordinal : Nat) (adversary : Adversary) (parameter : PublicParameter)
    (table : OtsSecretIndex → HashOutput)
    (ftsSecret : Index → FtsTree → FtsLeaf → Digest)
    (context : DeferredContext) (fuel : Nat)
    (value : Digest × SplitHashCache) (candidates : List Probe) :
    ProbComp (Option PrivateOrdinalSelection) :=
  directDetailedBoundaryPrivateOrdinalSelection ordinal parameter value.1 ftsSecret
    (retainedGameRestComputation adversary ⟨value.1, parameter⟩) candidates context fuel table
    value.2

instance granularPrivateOrdinalFinalizationObserve_observerDooms
    (ordinal : Nat) (adversary : Adversary) (parameter : PublicParameter)
    (table : OtsSecretIndex → HashOutput)
    (ftsSecret : Index → FtsTree → FtsLeaf → Digest)
    (target : Position) (rightRoot : Digest) :
    ObserverDooms table
      (granularPrivateOrdinalFinalizationObserve ordinal adversary parameter table ftsSecret
        target rightRoot) where
  eq_true context fuel value hconsistent hstarts hdoomed := by
    exact directBoundaryPrivateOrdinalFinalizationRisk_dooms ordinal parameter value.1 ftsSecret
      target rightRoot (retainedGameRestComputation adversary ⟨value.1, parameter⟩) [] context
      fuel table value.2 hconsistent hstarts hdoomed

instance granularPrivateOrdinalFinalizationObserve_observerSynchronized
    (ordinal : Nat) (adversary : Adversary) (parameter : PublicParameter)
    (table : OtsSecretIndex → HashOutput)
    (ftsSecret : Index → FtsTree → FtsLeaf → Digest)
    (target : Position) (rightRoot : Digest) :
    ObserverSynchronized table
      (granularPrivateOrdinalFinalizationObserve ordinal adversary parameter table ftsSecret
        target rightRoot) where
  eq_of_synchronized left right fuel value hcontext hvalues hrevealed := by
    exact directBoundaryPrivateOrdinalFinalizationRisk_synchronized ordinal parameter value.1
      ftsSecret target rightRoot (retainedGameRestComputation adversary ⟨value.1, parameter⟩)
      [] left right fuel table value.2 hcontext hvalues hrevealed

instance granularPrivateOrdinalFinalizationObserve_observerPositionNeutral
    (ordinal : Nat) (adversary : Adversary) (parameter : PublicParameter)
    (table : OtsSecretIndex → HashOutput)
    (ftsSecret : Index → FtsTree → FtsLeaf → Digest)
    (target : Position) (rightRoot : Digest) :
    ObserverPositionNeutral table
      (granularPrivateOrdinalFinalizationObserve ordinal adversary parameter table ftsSecret
        target rightRoot) where
  eq_resolve position context fuel value hvalid hcompletable hensured := by
    exact evalDist_resolveDeferredPositionValue_then_directBoundaryPrivateOrdinalFinalizationRisk
      ordinal parameter value.1 ftsSecret target rightRoot position
      (retainedGameRestComputation adversary ⟨value.1, parameter⟩) [] context fuel table value.2
      hvalid hcompletable hensured

noncomputable def granularAllCanonicalPrivateOrdinalFinalizationRisk
    (ordinal : Nat) (adversary : Adversary) (parameter : PublicParameter)
    (table : OtsSecretIndex → HashOutput)
    (ftsSecret : Index → FtsTree → FtsLeaf → Digest)
    (fuel : Nat) (target : Position) (rightRoot : Digest) : ProbComp Bool :=
  runResolvedObserve
    (canonicalizeObserve table
      (granularPrivateOrdinalFinalizationObserve ordinal adversary parameter table ftsSecret
        target rightRoot))
    emptyWitnessDeferredContext fuel table (maskedPublishedTreeRoot.run emptySplitHashCache)

theorem relTriple_granularPrivateOrdinalSelectionObserve_finalizationObserve
    (ordinal : Nat) (adversary : Adversary) (parameter : PublicParameter)
    (table : OtsSecretIndex → HashOutput)
    (ftsSecret : Index → FtsTree → FtsLeaf → Digest)
    (target : Position) (rightRoot : Digest)
    (context : DeferredContext) (fuel : Nat) (value : Digest × SplitHashCache)
    (hvalid : context.Valid) (hcompletable : DeferredCompletable table context) :
    RelTriple
      (granularPrivateOrdinalSelectionObserve ordinal adversary parameter table ftsSecret
        context fuel value [])
      (granularPrivateOrdinalFinalizationObserve ordinal adversary parameter table ftsSecret
        target rightRoot context fuel value)
      (PrivateOrdinalRootRiskRel target rightRoot ordinal) := by
  exact relTriple_directBoundaryPrivateOrdinalSelection_finalizationRisk ordinal parameter
    value.1 ftsSecret target rightRoot
    (retainedGameRestComputation adversary ⟨value.1, parameter⟩) [] context fuel table value.2
    hvalid hcompletable

theorem relTriple_canonicalGranularPrivateOrdinalSelection_finalizationObserve
    (ordinal : Nat) (adversary : Adversary) (parameter : PublicParameter)
    (table : OtsSecretIndex → HashOutput)
    (ftsSecret : Index → FtsTree → FtsLeaf → Digest)
    (target : Position) (rightRoot : Digest)
    (context : DeferredContext) (fuel : Nat) (value : Digest × SplitHashCache)
    (hconsistent : context.ValuesConsistent) :
    RelTriple
      (canonicalizeDirectPrivateOrdinalSelection table
        (granularPrivateOrdinalSelectionObserve ordinal adversary parameter table ftsSecret)
        context fuel value [])
      (canonicalizeObserve table
        (granularPrivateOrdinalFinalizationObserve ordinal adversary parameter table ftsSecret
          target rightRoot) context fuel value)
      (PrivateOrdinalRootRiskRel target rightRoot ordinal) := by
  apply relTriple_canonicalSelection_canonicalObserve table target rightRoot ordinal
    (granularPrivateOrdinalSelectionObserve ordinal adversary parameter table ftsSecret)
    (granularPrivateOrdinalFinalizationObserve ordinal adversary parameter table ftsSecret target
      rightRoot) context fuel value []
  intro _hpublished hcanonicalCompletable
  have hcanonicalConsistent := canonicalizeMaterializedValues_valuesConsistent table context
    hconsistent
  have hcanonicalStarts := canonicalizeMaterializedValues_startTableAgrees table context
  have hcanonicalValid := valid_of_resolvedCore_completable table
    (canonicalizeMaterializedValues table context) hcanonicalConsistent hcanonicalStarts
    hcanonicalCompletable
  exact relTriple_granularPrivateOrdinalSelectionObserve_finalizationObserve ordinal adversary
    parameter table ftsSecret target rightRoot (canonicalizeMaterializedValues table context) fuel
    value hcanonicalValid hcanonicalCompletable

attribute [local irreducible] maskedPublishedTreeRoot in
set_option maxRecDepth 100000 in
set_option maxHeartbeats 4000000 in
theorem relTriple_granularAllCanonicalPrivateOrdinalSelection_finalizationRisk
    (ordinal : Nat) (adversary : Adversary) (parameter : PublicParameter)
    (table : OtsSecretIndex → HashOutput)
    (ftsSecret : Index → FtsTree → FtsLeaf → Digest)
    (fuel : Nat) (target : Position) (rightRoot : Digest) :
    RelTriple
      (granularAllCanonicalPrivateOrdinalSelection ordinal adversary parameter table ftsSecret fuel)
      (granularAllCanonicalPrivateOrdinalFinalizationRisk ordinal adversary parameter table
        ftsSecret fuel target rightRoot)
      (PrivateOrdinalRootRiskRel target rightRoot ordinal) := by
  unfold granularAllCanonicalPrivateOrdinalSelection
    granularAllCanonicalPrivateOrdinalFinalizationRisk
  change RelTriple
    (runDirectResolvedWitnessFromTable emptyWitnessDeferredContext fuel table
        (maskedPublishedTreeRoot.run emptySplitHashCache) >>=
      finishDirectPrivateOrdinalSelection
        (canonicalizeDirectPrivateOrdinalSelection table
          (granularPrivateOrdinalSelectionObserve ordinal adversary parameter table ftsSecret)) [])
    (runResolvedObserve
      (canonicalizeObserve table
        (granularPrivateOrdinalFinalizationObserve ordinal adversary parameter table ftsSecret
          target rightRoot))
      emptyWitnessDeferredContext fuel table (maskedPublishedTreeRoot.run emptySplitHashCache))
    (PrivateOrdinalRootRiskRel target rightRoot ordinal)
  apply relTriple_runWitnessSelection_runResolvedObserve table target rightRoot ordinal
    (canonicalizeDirectPrivateOrdinalSelection table
      (granularPrivateOrdinalSelectionObserve ordinal adversary parameter table ftsSecret))
    (canonicalizeObserve table
      (granularPrivateOrdinalFinalizationObserve ordinal adversary parameter table ftsSecret target
        rightRoot)) [] emptyWitnessDeferredContext fuel
    (maskedPublishedTreeRoot.run emptySplitHashCache) DeferredContext.valid_empty
    (deferredCompletable_empty table)
  intro result hresult
  have hcore := resolvedCore_of_done_runDirectResolvedDetailedFromTable
    (maskedPublishedTreeRoot.run emptySplitHashCache) emptyWitnessDeferredContext fuel table result
    DeferredContext.valid_empty.valuesConsistent (startTableAgrees_empty table) hresult
  exact relTriple_canonicalGranularPrivateOrdinalSelection_finalizationObserve ordinal adversary
    parameter table ftsSecret target rightRoot result.context result.remaining result.value
    hcore.2.1

theorem probEvent_privateOrdinalSelectionGoodForSomeOutput_le_finalizationRisk
    (ordinal : Nat) (adversary : Adversary) (parameter : PublicParameter)
    (table : OtsSecretIndex → HashOutput)
    (ftsSecret : Index → FtsTree → FtsLeaf → Digest)
    (fuel : Nat) (target : Position) (rightRoot : Digest) :
    Pr[privateOrdinalSelectionGoodForSomeOutput target rightRoot ordinal |
        granularAllCanonicalPrivateOrdinalSelection ordinal adversary parameter table ftsSecret
          fuel] ≤
      Pr[= true | granularAllCanonicalPrivateOrdinalFinalizationRisk ordinal adversary parameter
        table ftsSecret fuel target rightRoot] := by
  calc
    _ ≤ Pr[fun hit : Bool => hit = true |
          granularAllCanonicalPrivateOrdinalFinalizationRisk ordinal adversary parameter table
            ftsSecret fuel target rightRoot] := by
      apply probEvent_le_of_relTriple
        (relTriple_granularAllCanonicalPrivateOrdinalSelection_finalizationRisk ordinal adversary
          parameter table ftsSecret fuel target rightRoot)
      intro selection hit hrelation hgood
      exact hrelation hgood
    _ = _ := probEvent_eq_eq_probOutput _ true

noncomputable def eagerGranularAllCanonicalPrivateOrdinalFinalizationRisk
    (ordinal : Nat) (adversary : Adversary) (parameter : PublicParameter)
    (table : OtsSecretIndex → HashOutput)
    (ftsSecret : Index → FtsTree → FtsLeaf → Digest)
    (fuel : Nat) (target : Position) (rightRoot : Digest) : ProbComp Bool := do
  let resolved ← resolveDeferredPositionValue target emptyWitnessDeferredContext
  match resolved with
  | none => pure true
  | some resolved =>
      runResolvedObserve
        (canonicalizeObserve table
          (granularPrivateOrdinalFinalizationObserve ordinal adversary parameter table ftsSecret
            target rightRoot))
        resolved.toDeferredContext fuel table
        (maskedPublishedTreeRoot.run emptySplitHashCache)

theorem evalDist_eagerGranularAllCanonicalPrivateOrdinalFinalizationRisk_eq
    (ordinal : Nat) (adversary : Adversary) (parameter : PublicParameter)
    (table : OtsSecretIndex → HashOutput)
    (ftsSecret : Index → FtsTree → FtsLeaf → Digest)
    (fuel : Nat) (target : Position) (rightRoot : Digest) :
    evalDist (eagerGranularAllCanonicalPrivateOrdinalFinalizationRisk ordinal adversary parameter
        table ftsSecret fuel target rightRoot) =
      evalDist (granularAllCanonicalPrivateOrdinalFinalizationRisk ordinal adversary parameter
        table ftsSecret fuel target rightRoot) := by
  unfold eagerGranularAllCanonicalPrivateOrdinalFinalizationRisk
    granularAllCanonicalPrivateOrdinalFinalizationRisk
  exact evalDist_resolveDeferredPositionValue_then_runResolvedObserve_any target
    (maskedPublishedTreeRoot.run emptySplitHashCache) emptyWitnessDeferredContext fuel table
    DeferredContext.valid_empty (deferredCompletable_empty table)

noncomputable def eagerGranularPrivateOrdinalFinalizationRiskAfterOutput
    (ordinal : Nat) (adversary : Adversary) (parameter : PublicParameter)
    (table : OtsSecretIndex → HashOutput)
    (ftsSecret : Index → FtsTree → FtsLeaf → Digest)
    (fuel : Nat) (target : Position) (rightRoot : Digest)
    (output : HashOutput) : ProbComp Bool :=
  runResolvedObserve
    (canonicalizeObserve table
      (granularPrivateOrdinalFinalizationObserve ordinal adversary parameter table ftsSecret
        target rightRoot))
    { emptyWitnessDeferredContext with
      values := emptyWitnessDeferredContext.values.install target output }
    fuel table (maskedPublishedTreeRoot.run emptySplitHashCache)

theorem evalDist_eagerGranularAllCanonicalPrivateOrdinalFinalizationRisk_eq_sample
    (ordinal : Nat) (adversary : Adversary) (parameter : PublicParameter)
    (table : OtsSecretIndex → HashOutput)
    (ftsSecret : Index → FtsTree → FtsLeaf → Digest)
    (fuel : Nat) (target : Position) (rightRoot : Digest) :
    evalDist (eagerGranularAllCanonicalPrivateOrdinalFinalizationRisk ordinal adversary parameter
        table ftsSecret fuel target rightRoot) =
      evalDist (LazyRevealProbe.sampleHashOutput >>= fun output =>
        eagerGranularPrivateOrdinalFinalizationRiskAfterOutput ordinal adversary parameter table
          ftsSecret fuel target rightRoot output) := by
  unfold eagerGranularAllCanonicalPrivateOrdinalFinalizationRisk
    eagerGranularPrivateOrdinalFinalizationRiskAfterOutput
    resolveDeferredPositionValue emptyWitnessDeferredContext
  simp [LazyRevealProbe.State.empty, LazyRevealProbe.State.hitAt,
    LazyRevealProbe.State.pendingAt, LazyRevealProbe.State.clearPending,
    LazyRevealProbe.State.pendingAway,
    emptyDeferredStructuralValues]

theorem evalDist_eagerGranularAllCanonicalPrivateOrdinalFinalizationRisk_eq_rootParts
    (ordinal : Nat) (adversary : Adversary) (parameter : PublicParameter)
    (table : OtsSecretIndex → HashOutput)
    (ftsSecret : Index → FtsTree → FtsLeaf → Digest)
    (fuel : Nat) (target : Position) (rightRoot : Digest) :
    evalDist (eagerGranularAllCanonicalPrivateOrdinalFinalizationRisk ordinal adversary parameter
        table ftsSecret fuel target rightRoot) =
      evalDist (do
        let leftRoot ← ($ᵗ Digest : ProbComp Digest)
        let high ← ($ᵗ RootOutputHigh : ProbComp RootOutputHigh)
        eagerGranularPrivateOrdinalFinalizationRiskAfterOutput ordinal adversary parameter table
          ftsSecret fuel target rightRoot (rootOutputOfParts leftRoot high)) := by
  rw [evalDist_eagerGranularAllCanonicalPrivateOrdinalFinalizationRisk_eq_sample]
  let parts : ProbComp HashOutput := do
    let leftRoot ← ($ᵗ Digest : ProbComp Digest)
    let high ← ($ᵗ RootOutputHigh : ProbComp RootOutputHigh)
    pure (rootOutputOfParts leftRoot high)
  calc
    _ = evalDist (parts >>= fun output =>
          eagerGranularPrivateOrdinalFinalizationRiskAfterOutput ordinal adversary parameter table
            ftsSecret fuel target rightRoot output) := by
      rw [evalDist_bind, evalDist_bind, show evalDist parts =
        evalDist LazyRevealProbe.sampleHashOutput from evalDist_sample_rootOutputOfParts]
    _ = _ := by simp [parts, bind_assoc]

end SphincsSecurity.Concrete.OtsProbeSimulation
