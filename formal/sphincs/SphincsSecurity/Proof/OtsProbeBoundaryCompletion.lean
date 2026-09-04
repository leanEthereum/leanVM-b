import SphincsSecurity.Proof.OtsProbeResolvedBoundaryWitnessOrdinary
import SphincsSecurity.Proof.OtsProbeVerifierBoundary

/-! The canonical boundary fails only through a private witness or materialized ordinary failure. Guarded completion identifies the latter with the diagnostic bad event, and the verifier bridge transfers their combined bound to the original experiment. -/

namespace SphincsSecurity.Concrete.OtsProbeSimulation

open OracleComp OracleSpec ENNReal

def ObservedMaterializedDiagnostic.guardedFinal
    (outcome : ObservedMaterializedDiagnostic α) : Option (ObservedCleanRunResult α) :=
  if outcome.wasDoomed then none else outcome.final

theorem guardedFinal_eq_none_iff (outcome : ObservedMaterializedDiagnostic α) :
    outcome.guardedFinal = none ↔ outcome.Bad := by
  cases outcome with
  | mk before final wasDoomed =>
      cases wasDoomed <;>
        simp [ObservedMaterializedDiagnostic.guardedFinal, ObservedMaterializedDiagnostic.Bad]

theorem evalDist_guardedFinal_finishObservedMaterializedDiagnostic
    (table : OtsSecretIndex → HashOutput)
    (result : Option (ObservedCleanRunResult α)) :
    evalDist (ObservedMaterializedDiagnostic.guardedFinal <$>
        finishObservedMaterializedDiagnostic table result) =
      evalDist (finishObservedMaterializedCleanRunFromTable table result) := by
  classical
  cases result with
  | none => rfl
  | some result =>
      by_cases hcomplete : DeferredCompletable table (directDeferredContext result.state)
      · simp [finishObservedMaterializedDiagnostic, finishObservedMaterializedCleanRunFromTable,
          ObservedMaterializedDiagnostic.guardedFinal, hcomplete]
      · simp only [finishObservedMaterializedDiagnostic, finishObservedMaterializedCleanRunFromTable,
          ObservedMaterializedDiagnostic.guardedFinal, hcomplete, not_false_eq_true, decide_true,
          if_true, if_false, map_bind, map_pure]
        exact OracleComp.DeferredSampling.evalDist_bind_const_neverFails
          (finishObservedCleanRunFromTable (some result)) (by simp [finishObservedCleanRunFromTable])
          (pure none)

theorem evalDist_guardedFinal_sampledObservedMaterializedDiagnostic
    (adversary : Adversary) (parameter : PublicParameter)
    (ftsSecret : Index → FtsTree → FtsLeaf → Digest) (fuel : Nat) :
    evalDist (ObservedMaterializedDiagnostic.guardedFinal <$>
        sampledObservedMaterializedDiagnostic adversary parameter ftsSecret fuel) =
      evalDist (sampledObservedMaterializedClean adversary parameter ftsSecret fuel) := by
  unfold sampledObservedMaterializedDiagnostic sampledObservedMaterializedClean
  rw [map_bind]
  apply evalDist_bind_congr
  intro table _
  rw [map_bind]
  apply evalDist_bind_congr
  intro result _
  exact evalDist_guardedFinal_finishObservedMaterializedDiagnostic table result

theorem probEvent_sampledMaterializedClean_none_eq_diagnosticBad
    (adversary : Adversary) (parameter : PublicParameter)
    (ftsSecret : Index → FtsTree → FtsLeaf → Digest) (fuel : Nat) :
    Pr[= none | sampledMaterializedClean adversary parameter ftsSecret fuel] =
      Pr[ObservedMaterializedDiagnostic.Bad |
        sampledObservedMaterializedDiagnostic adversary parameter ftsSecret fuel] := by
  rw [← probEvent_sampledObservedMaterializedClean_none_eq_clean]
  calc
    _ = Pr[= none | ObservedMaterializedDiagnostic.guardedFinal <$>
        sampledObservedMaterializedDiagnostic adversary parameter ftsSecret fuel] :=
      OracleComp.probOutput_congr rfl
        (evalDist_guardedFinal_sampledObservedMaterializedDiagnostic adversary parameter
          ftsSecret fuel).symm
    _ = _ := by
      rw [← probEvent_eq_eq_probOutput, probEvent_map]
      apply OracleComp.probEvent_congr'
      · intro outcome _
        exact guardedFinal_eq_none_iff outcome
      · rfl

theorem probEvent_sampledMaterializedClean_none_le_five_mul
    (adversary : Adversary) (parameter : PublicParameter)
    (ftsSecret : Index → FtsTree → FtsLeaf → Digest) (q : Nat)
    (hexpanded : ∀ table root,
      (simulateQ
        (SphincsSecurity.expandedAdversaryImpl
          (⟨parameter, root, tableOtsSecret (extendStartTable table), ftsSecret⟩ : SecretKey))
        (retainedGameRestComputation adversary ⟨root, parameter⟩)).IsQueryBoundP
          (fun query => query matches Sum.inr _) q)
    (hq : q ≤ 2 ^ securityBits) :
    Pr[= none | sampledMaterializedClean adversary parameter ftsSecret (2 * q)] ≤
      ((5 * q : Nat) : ENNReal) * ((2 ^ digestBits : Nat) : ENNReal)⁻¹ := by
  rw [probEvent_sampledMaterializedClean_none_eq_diagnosticBad]
  apply probEvent_sampledDiagnostic_bad_le_five_mul adversary parameter ftsSecret q
    _ hexpanded hq
  rw [show Fintype.card Digest = 2 ^ digestBits by simp]
  norm_num [securityBits, digestBits] at hq ⊢
  omega

theorem evalDist_runDirectDetailedOrdinary_eq_cleanFailureObserve
    (computation : OracleComp (LazyRevealProbe.World Coordinate) α)
    (observe : DeferredContext → Nat → α → ProbComp Bool)
    (state : LazyRevealProbe.State Coordinate) (fuel : Nat)
    (table : OtsSecretIndex → HashOutput) :
    evalDist (runDirectDetailedOrdinaryObserve observe
        (directDeferredContext state) fuel table computation) =
      evalDist (runCleanFromTable state fuel table computation >>=
        finishCleanFailureObserve (fun _ nextState remaining value =>
          observe (directDeferredContext nextState) remaining value)) := by
  unfold runDirectDetailedOrdinaryObserve
  rw [← map_projectDirectDetailedClean_run_eq_clean computation state fuel table,
    map_eq_bind_pure_comp, bind_assoc]
  apply evalDist_bind_congr
  intro result hresult
  have hshape := directDetailedMaterialized_of_mem_runDirectResolvedDetailedFromTable
    computation state fuel table result hresult
  cases result with
  | stopped reason =>
      cases reason with
      | privateStructuralHit => exact False.elim hshape
      | ordinaryHit => rfl
      | fuelExhausted => rfl
  | done result =>
      simp only [finishDirectDetailedOrdinaryObserve, Function.comp_apply, pure_bind,
        projectDirectDetailedClean, DirectDetailedResult.toOption, projectResolvedRunResult,
        finishCleanFailureObserve]
      change evalDist (observe result.context result.remaining result.value) =
        evalDist (observe (directDeferredContext result.context.state)
          result.remaining result.value)
      rw [show result.context = directDeferredContext result.context.state from hshape]
      rfl

theorem deferredCompletable_of_mem_runCleanFromTable
    (computation : OracleComp (LazyRevealProbe.World Coordinate) α)
    (state : LazyRevealProbe.State Coordinate) (fuel : Nat)
    (table : OtsSecretIndex → HashOutput) (result : CleanRunResult α)
    (hstarts : StartTableAgrees state table)
    (hresult : some result ∈ support (runCleanFromTable state fuel table computation))
    (hfinal : DeferredCompletable table (directDeferredContext result.state)) :
    DeferredCompletable table (directDeferredContext state) := by
  rw [← map_projectDirectDetailedClean_run_eq_clean computation state fuel table,
    support_map] at hresult
  obtain ⟨detailed, hdetailed, hproject⟩ := hresult
  have hshape := directDetailedMaterialized_of_mem_runDirectResolvedDetailedFromTable
    computation state fuel table detailed hdetailed
  cases detailed with
  | stopped reason =>
      simp [projectDirectDetailedClean, DirectDetailedResult.toOption,
        projectResolvedRunResult] at hproject
  | done detailed =>
      have heq : result =
          ⟨detailed.context.state, detailed.remaining, detailed.value, detailed.table⟩ :=
        Option.some.inj (by simpa [projectDirectDetailedClean,
          DirectDetailedResult.toOption, projectResolvedRunResult] using hproject.symm)
      subst result
      apply deferredCompletable_of_mem_runDirectResolvedFromTable computation
        (directDeferredContext state) fuel table detailed (fun _ _ h => h) hstarts
        (mem_support_runDirectResolvedFromTable_of_done_detailed computation
          (directDeferredContext state) fuel table detailed hdetailed)
      rwa [show detailed.context = directDeferredContext detailed.context.state from hshape]

theorem completion_of_mem_materializedCleanBoundary
    (parameter : PublicParameter) (root : Digest)
    (ftsSecret : Index → FtsTree → FtsLeaf → Digest)
    (computation : OracleComp (OracleWorld + SigningSpec) α)
    (state : LazyRevealProbe.State Coordinate) (fuel : Nat)
    (table : OtsSecretIndex → HashOutput) (cache : SplitHashCache)
    (result : CleanRunResult (α × SplitHashCache))
    (hstarts : StartTableAgrees state table)
    (hresult : some result ∈ support
      (materializedCleanBoundary parameter root ftsSecret computation state fuel table cache)) :
    result.table = table ∧ StartTableAgrees result.state table ∧
      (DeferredCompletable table (directDeferredContext result.state) →
        DeferredCompletable table (directDeferredContext state)) := by
  induction computation using OracleComp.inductionOn generalizing state fuel cache with
  | pure value =>
      simp [materializedCleanBoundary] at hresult
      subst result
      exact ⟨rfl, hstarts, fun h => h⟩
  | query_bind query next ih =>
      rw [materializedCleanBoundary, OracleComp.construct_query_bind] at hresult
      cases query with
      | inl world =>
          cases world with
          | inl n =>
              simp only [mem_support_bind_iff] at hresult
              obtain ⟨step, hstep, htail⟩ := hresult
              cases step with
              | none => simp at htail
              | some step =>
                  have hstepStarts := startTableAgrees_of_mem_runCleanFromTable _ state fuel table
                    hstarts step hstep
                  have hrest := ih step.value.1 step.state step.remaining step.value.2 hstepStarts.2 htail
                  exact ⟨hrest.1, hrest.2.1, fun hfinal =>
                    deferredCompletable_of_mem_runCleanFromTable _ state fuel table step hstarts hstep
                      (hrest.2.2 hfinal)⟩
          | inr input =>
              simp only [mem_support_bind_iff] at hresult
              obtain ⟨step, hstep, htail⟩ := hresult
              cases step with
              | none => simp at htail
              | some step =>
                  have hstepStarts := startTableAgrees_of_mem_runCleanFromTable _ state fuel table
                    hstarts step hstep
                  have hrest := ih step.value.1 step.state step.remaining step.value.2 hstepStarts.2 htail
                  exact ⟨hrest.1, hrest.2.1, fun hfinal =>
                    deferredCompletable_of_mem_runCleanFromTable _ state fuel table step hstarts hstep
                      (hrest.2.2 hfinal)⟩
      | inr message =>
          simp only [mem_support_bind_iff] at hresult
          obtain ⟨step, hstep, htail⟩ := hresult
          cases step with
          | none => simp at htail
          | some step =>
              have hstepStarts := startTableAgrees_of_mem_runCleanFromTable _ state fuel table
                hstarts step hstep
              have hrest := ih step.value.1 step.state step.remaining step.value.2 hstepStarts.2 htail
              exact ⟨hrest.1, hrest.2.1, fun hfinal =>
                deferredCompletable_of_mem_runCleanFromTable _ state fuel table step hstarts hstep
                  (hrest.2.2 hfinal)⟩

theorem evalDist_materializedCleanBoundary_eq_true_of_not_completable
    (parameter : PublicParameter) (root : Digest)
    (ftsSecret : Index → FtsTree → FtsLeaf → Digest)
    (computation : OracleComp (OracleWorld + SigningSpec) α)
    (observe : DeferredContext → Nat → (α × SplitHashCache) → ProbComp Bool)
    (state : LazyRevealProbe.State Coordinate) (fuel : Nat)
    (table : OtsSecretIndex → HashOutput) (cache : SplitHashCache)
    (hstarts : StartTableAgrees state table)
    (hdoomed : ¬DeferredCompletable table (directDeferredContext state))
    (hobserve : ∀ nextState remaining value, StartTableAgrees nextState table →
      ¬DeferredCompletable table (directDeferredContext nextState) →
      evalDist (observe (directDeferredContext nextState) remaining value) =
        evalDist (pure true : ProbComp Bool)) :
    evalDist (materializedCleanBoundary parameter root ftsSecret computation state fuel table
        cache >>= finishCleanFailureObserve (fun _ nextState remaining value =>
          observe (directDeferredContext nextState) remaining value)) =
      evalDist (pure true : ProbComp Bool) := by
  calc
    _ = evalDist (materializedCleanBoundary parameter root ftsSecret computation state fuel table
        cache >>= fun _ => (pure true : ProbComp Bool)) := by
      apply evalDist_bind_congr
      intro result hresult
      cases result with
      | none => rfl
      | some result =>
          have hcomplete := completion_of_mem_materializedCleanBoundary parameter root
            ftsSecret computation state fuel table cache result hstarts hresult
          exact hobserve result.state result.remaining result.value hcomplete.2.1
            (fun hfinal => hdoomed (hcomplete.2.2 hfinal))
    _ = _ := OracleComp.DeferredSampling.evalDist_bind_const_neverFails _ (by simp) _

theorem evalDist_rootAwareMaterializedBoundaryOrdinary_eq_clean
    (parameter : PublicParameter) (root : Digest)
    (ftsSecret : Index → FtsTree → FtsLeaf → Digest)
    (computation : OracleComp (OracleWorld + SigningSpec) α)
    (observe : DeferredContext → Nat → (α × SplitHashCache) → ProbComp Bool)
    (state : LazyRevealProbe.State Coordinate) (fuel : Nat)
    (table : OtsSecretIndex → HashOutput) (cache : SplitHashCache)
    (hstarts : StartTableAgrees state table)
    (hobserve : ∀ nextState remaining value, StartTableAgrees nextState table →
      ¬DeferredCompletable table (directDeferredContext nextState) →
      evalDist (observe (directDeferredContext nextState) remaining value) =
        evalDist (pure true : ProbComp Bool)) :
    evalDist (rootAwareMaterializedDetailedBoundaryOrdinaryObserve parameter root ftsSecret
        computation observe (directDeferredContext state) fuel table cache) =
      evalDist (materializedCleanBoundary parameter root ftsSecret computation state fuel table
        cache >>= finishCleanFailureObserve (fun _ nextState remaining value =>
          observe (directDeferredContext nextState) remaining value)) := by
  induction computation using OracleComp.inductionOn generalizing state fuel cache with
  | pure value =>
      simp [rootAwareMaterializedDetailedBoundaryOrdinaryObserve, materializedCleanBoundary,
        finishCleanFailureObserve]
  | query_bind query next ih =>
      rw [rootAwareMaterializedDetailedBoundaryOrdinaryObserve, OracleComp.construct_query_bind,
        materializedCleanBoundary, OracleComp.construct_query_bind]
      cases query with
      | inl world =>
          cases world with
          | inl n =>
              rw [evalDist_runDirectDetailedOrdinary_eq_cleanFailureObserve, bind_assoc]
              apply evalDist_bind_congr
              intro step hstep
              cases step with
              | none => rfl
              | some step =>
                  have hstepStarts := startTableAgrees_of_mem_runCleanFromTable _ state fuel table
                    hstarts step hstep
                  have hnotPrivate := not_privateStructuralHit_of_directDeferredContext
                    (directDeferredContext step.state) rfl
                  simp only [finishCleanFailureObserve]
                  by_cases hcomplete : DeferredCompletable table (directDeferredContext step.state)
                  · simp only [classifyDirectDetailedOrdinaryObserve, hnotPrivate, hcomplete, ↓reduceIte]
                    exact ih step.value.1 step.state step.remaining step.value.2 hstepStarts.2
                  · simp only [classifyDirectDetailedOrdinaryObserve, hnotPrivate, hcomplete, ↓reduceIte]
                    exact (evalDist_materializedCleanBoundary_eq_true_of_not_completable parameter root
                      ftsSecret (next step.value.1) observe step.state step.remaining table step.value.2
                      hstepStarts.2 hcomplete hobserve).symm
          | inr input =>
              rw [evalDist_runDirectDetailedOrdinary_eq_cleanFailureObserve, bind_assoc]
              apply evalDist_bind_congr
              intro step hstep
              cases step with
              | none => rfl
              | some step =>
                  have hstepStarts := startTableAgrees_of_mem_runCleanFromTable _ state fuel table
                    hstarts step hstep
                  have hnotPrivate := not_privateStructuralHit_of_directDeferredContext
                    (directDeferredContext step.state) rfl
                  simp only [finishCleanFailureObserve]
                  by_cases hcomplete : DeferredCompletable table (directDeferredContext step.state)
                  · simp only [classifyDirectDetailedOrdinaryObserve, hnotPrivate, hcomplete, ↓reduceIte]
                    exact ih step.value.1 step.state step.remaining step.value.2 hstepStarts.2
                  · simp only [classifyDirectDetailedOrdinaryObserve, hnotPrivate, hcomplete, ↓reduceIte]
                    exact (evalDist_materializedCleanBoundary_eq_true_of_not_completable parameter root
                      ftsSecret (next step.value.1) observe step.state step.remaining table step.value.2
                      hstepStarts.2 hcomplete hobserve).symm
      | inr message =>
          rw [evalDist_runDirectDetailedOrdinary_eq_cleanFailureObserve, bind_assoc]
          apply evalDist_bind_congr
          intro step hstep
          cases step with
          | none => rfl
          | some step =>
              have hstepStarts := startTableAgrees_of_mem_runCleanFromTable _ state fuel table
                hstarts step hstep
              have hnotPrivate := not_privateStructuralHit_of_directDeferredContext
                (directDeferredContext step.state) rfl
              simp only [finishCleanFailureObserve]
              by_cases hcomplete : DeferredCompletable table (directDeferredContext step.state)
              · simp only [classifyDirectDetailedOrdinaryObserve, hnotPrivate, hcomplete, ↓reduceIte]
                exact ih step.value.1 step.state step.remaining step.value.2 hstepStarts.2
              · simp only [classifyDirectDetailedOrdinaryObserve, hnotPrivate, hcomplete, ↓reduceIte]
                exact (evalDist_materializedCleanBoundary_eq_true_of_not_completable parameter root
                  ftsSecret (next step.value.1) observe step.state step.remaining table step.value.2
                  hstepStarts.2 hcomplete hobserve).symm

theorem evalDist_classifyResolvedFinalization_direct_eq_guarded
    (table : OtsSecretIndex → HashOutput)
    (state : LazyRevealProbe.State Coordinate) (fuel : Nat) (value : α) :
    evalDist (classifyDirectOrdinaryObserve table (resolvedFinalizationObserve table)
        (directDeferredContext state) fuel value) =
      evalDist (Option.isNone <$>
        finishMaterializedCleanRunFromTable table (some ⟨state, fuel, value, table⟩)) := by
  classical
  have hnotPrivate := not_privateStructuralHit_of_directDeferredContext
    (directDeferredContext state) rfl
  by_cases hcomplete : DeferredCompletable table (directDeferredContext state)
  · simp only [classifyDirectOrdinaryObserve, hnotPrivate, hcomplete, ↓reduceIte,
      finishMaterializedCleanRunFromTable]
    exact evalDist_finishResolvedRunIsNone_eq_finishDirectRunIsNone state fuel value table
      hcomplete
  · simp [classifyDirectOrdinaryObserve, hnotPrivate, hcomplete,
      finishMaterializedCleanRunFromTable]

theorem retainedFinalizationOrdinary_dooms
    (table : OtsSecretIndex → HashOutput) (root : Digest)
    (state : LazyRevealProbe.State Coordinate) (fuel : Nat)
    (value : RetainedRestResult × SplitHashCache)
    (hdoomed : ¬DeferredCompletable table (directDeferredContext state)) :
    evalDist (retainedResolvedFinalizationOrdinaryObserve table root
        (directDeferredContext state) fuel value) =
      evalDist (pure true : ProbComp Bool) := by
  have hnotPrivate := not_privateStructuralHit_of_directDeferredContext
    (directDeferredContext state) rfl
  simp [retainedResolvedFinalizationOrdinaryObserve, classifyDirectOrdinaryObserve,
    hnotPrivate, hdoomed]

theorem evalDist_rootAwareRetainedRestOrdinary_eq_guardedClean
    (adversary : Adversary) (parameter : PublicParameter)
    (table : OtsSecretIndex → HashOutput)
    (ftsSecret : Index → FtsTree → FtsLeaf → Digest)
    (state : LazyRevealProbe.State Coordinate) (fuel : Nat)
    (value : Digest × SplitHashCache) (hstarts : StartTableAgrees state table) :
    evalDist (rootAwareMaterializedDetailedRetainedRestOrdinaryObserve adversary parameter
        table ftsSecret (directDeferredContext state) fuel value) =
      evalDist (do
        let result ← materializedCleanBoundary parameter value.1 ftsSecret
          (retainedGameRestComputation adversary ⟨value.1, parameter⟩) state fuel table value.2
        let final ← finishMaterializedCleanRunFromTable table
          (result.map fun (result : CleanRunResult (RetainedRestResult × SplitHashCache)) =>
            (⟨result.state, result.remaining, ((value.1, result.value.1), result.value.2),
              result.table⟩ : CleanRunResult (RetainedGameResult × SplitHashCache)))
        pure final.isNone) := by
  unfold rootAwareMaterializedDetailedRetainedRestOrdinaryObserve
  rw [evalDist_rootAwareMaterializedBoundaryOrdinary_eq_clean parameter value.1 ftsSecret
    _ _ state fuel table value.2 hstarts
    (fun nextState remaining nextValue _ hdoomed =>
      retainedFinalizationOrdinary_dooms table value.1 nextState remaining nextValue hdoomed)]
  apply evalDist_bind_congr
  intro result hresult
  cases result with
  | none => rfl
  | some result =>
      have htable := (completion_of_mem_materializedCleanBoundary parameter value.1
        ftsSecret _ state fuel table value.2 result hstarts hresult).1
      simp only [finishCleanFailureObserve, retainedResolvedFinalizationOrdinaryObserve,
        Option.map_some, htable]
      exact evalDist_classifyResolvedFinalization_direct_eq_guarded table result.state
        result.remaining ((value.1, result.value.1), result.value.2)

theorem rootAwareRetainedRestOrdinary_dooms
    (adversary : Adversary) (parameter : PublicParameter)
    (table : OtsSecretIndex → HashOutput)
    (ftsSecret : Index → FtsTree → FtsLeaf → Digest)
    (state : LazyRevealProbe.State Coordinate) (fuel : Nat)
    (value : Digest × SplitHashCache) (hstarts : StartTableAgrees state table)
    (hdoomed : ¬DeferredCompletable table (directDeferredContext state)) :
    evalDist (rootAwareMaterializedDetailedRetainedRestOrdinaryObserve adversary parameter
        table ftsSecret (directDeferredContext state) fuel value) =
      evalDist (pure true : ProbComp Bool) := by
  unfold rootAwareMaterializedDetailedRetainedRestOrdinaryObserve
  have hobserve := fun nextState remaining nextValue (_ : StartTableAgrees nextState table)
    (hdoomed : ¬DeferredCompletable table (directDeferredContext nextState)) =>
      retainedFinalizationOrdinary_dooms table value.1 nextState remaining nextValue hdoomed
  rw [evalDist_rootAwareMaterializedBoundaryOrdinary_eq_clean parameter value.1 ftsSecret
    _ _ state fuel table value.2 hstarts hobserve]
  exact evalDist_materializedCleanBoundary_eq_true_of_not_completable parameter value.1
    ftsSecret _ _ state fuel table value.2 hstarts hdoomed hobserve

attribute [local irreducible] maskedPublishedTreeRoot in
theorem evalDist_rootAwareMaterializedRetainedOrdinary_eq_clean
    (adversary : Adversary) (parameter : PublicParameter)
    (table : OtsSecretIndex → HashOutput)
    (ftsSecret : Index → FtsTree → FtsLeaf → Digest) (fuel : Nat) :
    evalDist (rootAwareMaterializedBoundaryDetailedRetainedOrdinary adversary parameter table
        ftsSecret fuel) =
      evalDist (do
        let result ← materializedCleanRetainedRunFromTable adversary parameter ftsSecret
          (2 * fuel) table
        let final ← finishMaterializedCleanRunFromTable table result
        pure final.isNone) := by
  unfold rootAwareMaterializedBoundaryDetailedRetainedOrdinary
    materializedCleanRetainedRunFromTable
  rw [evalDist_runDirectDetailedOrdinary_eq_cleanFailureObserve, bind_assoc]
  apply evalDist_bind_congr
  intro result hresult
  cases result with
  | none => rfl
  | some result =>
      have hstarts := (startTableAgrees_of_mem_runCleanFromTable
        (maskedPublishedTreeRoot.run emptySplitHashCache) LazyRevealProbe.State.empty
        (2 * fuel) table (startTableAgrees_empty table) result hresult).2
      have hnotPrivate := not_privateStructuralHit_of_directDeferredContext
        (directDeferredContext result.state) rfl
      have hrest := evalDist_rootAwareRetainedRestOrdinary_eq_guardedClean adversary parameter
        table ftsSecret result.state result.remaining result.value hstarts
      simp only [finishCleanFailureObserve]
      by_cases hcomplete : DeferredCompletable table (directDeferredContext result.state)
      · simp only [classifyDirectDetailedOrdinaryObserve, hnotPrivate, hcomplete, ↓reduceIte]
        rw [hrest, bind_assoc]
        apply evalDist_bind_congr
        intro rest _
        cases rest <;> rfl
      · simp only [classifyDirectDetailedOrdinaryObserve, hnotPrivate, hcomplete, ↓reduceIte]
        rw [← rootAwareRetainedRestOrdinary_dooms adversary parameter table ftsSecret
          result.state result.remaining result.value hstarts hcomplete, hrest, bind_assoc]
        apply evalDist_bind_congr
        intro rest _
        cases rest <;> rfl

theorem probEvent_sampledRootAwareRetainedOrdinary_eq_clean
    (adversary : Adversary) (parameter : PublicParameter)
    (ftsSecret : Index → FtsTree → FtsLeaf → Digest) (fuel : Nat) :
    Pr[= true | sampledRootAwareMaterializedBoundaryDetailedRetainedOrdinary adversary
        parameter ftsSecret fuel] =
      Pr[= none | sampledMaterializedClean adversary parameter ftsSecret (2 * fuel)] := by
  have hdist : evalDist
      (sampledRootAwareMaterializedBoundaryDetailedRetainedOrdinary adversary parameter
        ftsSecret fuel) =
      evalDist (Option.isNone <$>
        sampledMaterializedClean adversary parameter ftsSecret (2 * fuel)) := by
    unfold sampledRootAwareMaterializedBoundaryDetailedRetainedOrdinary sampledMaterializedClean
    rw [map_bind]
    apply evalDist_bind_congr
    intro table _
    rw [map_bind]
    exact evalDist_rootAwareMaterializedRetainedOrdinary_eq_clean adversary parameter table
      ftsSecret fuel
  rw [OracleComp.probOutput_congr rfl hdist, ← probEvent_eq_eq_probOutput,
    probEvent_map, ← probEvent_eq_eq_probOutput]
  apply OracleComp.probEvent_congr'
  · intro result _
    simp
  · rfl

theorem probEvent_sampledRootAwareRetainedOrdinary_le_five_mul
    (adversary : Adversary) (parameter : PublicParameter)
    (ftsSecret : Index → FtsTree → FtsLeaf → Digest) (q : Nat)
    (hexpanded : ∀ table root,
      (simulateQ
        (SphincsSecurity.expandedAdversaryImpl
          (⟨parameter, root, tableOtsSecret (extendStartTable table), ftsSecret⟩ : SecretKey))
        (retainedGameRestComputation adversary ⟨root, parameter⟩)).IsQueryBoundP
          (fun query => query matches Sum.inr _) q)
    (hq : q ≤ 2 ^ securityBits) :
    Pr[= true | sampledRootAwareMaterializedBoundaryDetailedRetainedOrdinary adversary parameter
        ftsSecret q] ≤
      ((5 * q : Nat) : ENNReal) * ((2 ^ digestBits : Nat) : ENNReal)⁻¹ := by
  rw [probEvent_sampledRootAwareRetainedOrdinary_eq_clean]
  exact probEvent_sampledMaterializedClean_none_le_five_mul adversary parameter ftsSecret q
    hexpanded hq

theorem probEvent_sampledCanonicalBoundary_failed_le_thirteen_mul
    (adversary : Adversary) (parameter : PublicParameter)
    (ftsSecret : Index → FtsTree → FtsLeaf → Digest) (q : Nat)
    (hexpanded : ∀ table root,
      (simulateQ
        (SphincsSecurity.expandedAdversaryImpl
          (⟨parameter, root, tableOtsSecret (extendStartTable table), ftsSecret⟩ : SecretKey))
        (retainedGameRestComputation adversary ⟨root, parameter⟩)).IsQueryBoundP
          (fun query => query matches Sum.inr _) q)
    (hq : q ≤ 2 ^ securityBits) :
    Pr[fun output => output.outcome.failed = true |
        sampledGranularAllCanonicalBoundaryWitnessPlan adversary parameter ftsSecret q] ≤
      ((13 * q : Nat) : ENNReal) * ((2 ^ digestBits : Nat) : ENNReal)⁻¹ := by
  calc
    _ ≤ Pr[fun output => output.witnessPlan.1.isSome = true |
          sampledGranularAllCanonicalBoundaryWitnessPlan adversary parameter ftsSecret q] +
        Pr[fun outcome => outcome.ordinary = true |
          sampledRootAwareMaterializedBoundaryDetailedRetainedOutcome adversary parameter
            ftsSecret q] :=
      probEvent_sampledCanonicalBoundary_failed_le_witness_add_materializedOrdinary
        adversary parameter ftsSecret q hexpanded
    _ = Pr[fun output => output.1.isSome = true |
          sampledGranularAllCanonicalPrivateWitnessPlan adversary parameter ftsSecret q] +
        Pr[= true | sampledRootAwareMaterializedBoundaryDetailedRetainedOrdinary adversary
          parameter ftsSecret q] := by
      rw [probEvent_witness_sampledGranularAllCanonicalBoundaryWitnessPlan_eq,
        probEvent_ordinary_sampledRootAwareMaterializedBoundaryDetailedRetainedOutcome]
    _ ≤ ((8 * q : Nat) : ENNReal) * ((2 ^ digestBits : Nat) : ENNReal)⁻¹ +
        ((5 * q : Nat) : ENNReal) * ((2 ^ digestBits : Nat) : ENNReal)⁻¹ :=
      add_le_add
        (probEvent_sampledCanonical_privateWitnessPlan_le_eight_mul adversary parameter
          ftsSecret q hexpanded hq)
        (probEvent_sampledRootAwareRetainedOrdinary_le_five_mul adversary parameter
          ftsSecret q hexpanded hq)
    _ = _ := by
      push_cast
      ring

theorem probEvent_sampledCanonicalBoundary_finishIsNone_le_thirteen_mul
    (adversary : Adversary) (parameter : PublicParameter)
    (ftsSecret : Index → FtsTree → FtsLeaf → Digest) (q : Nat)
    (hexpanded : ∀ table root,
      (simulateQ
        (SphincsSecurity.expandedAdversaryImpl
          (⟨parameter, root, tableOtsSecret (extendStartTable table), ftsSecret⟩ : SecretKey))
        (retainedGameRestComputation adversary ⟨root, parameter⟩)).IsQueryBoundP
          (fun query => query matches Sum.inr _) q)
    (hq : q ≤ 2 ^ securityBits) :
    Pr[= true | sampledGranularAllCanonicalBoundaryRetainedFinishIsNone adversary parameter
        ftsSecret q] ≤
      ((13 * q : Nat) : ENNReal) * ((2 ^ digestBits : Nat) : ENNReal)⁻¹ := by
  have heq := OracleComp.probOutput_congr (show true = true from rfl)
    (evalDist_failed_sampledGranularAllCanonicalBoundaryWitnessPlan adversary parameter
      ftsSecret q)
  rw [← heq, ← probEvent_eq_eq_probOutput, probEvent_map]
  exact probEvent_sampledCanonicalBoundary_failed_le_thirteen_mul adversary parameter
    ftsSecret q hexpanded hq

attribute [local irreducible] maskedPublishedTreeRoot in
theorem evalDist_granularAllCanonicalBoundaryRetainedFinishIsNone_eq_allDirect
    (adversary : Adversary) (parameter : PublicParameter)
    (table : OtsSecretIndex → HashOutput)
    (ftsSecret : Index → FtsTree → FtsLeaf → Digest) (fuel : Nat) :
    evalDist (granularAllCanonicalBoundaryRetainedFinishIsNone adversary parameter table ftsSecret fuel) =
      evalDist (allDirectBoundaryDeferredRetainedFinishIsNone adversary parameter table ftsSecret fuel) := by
  unfold granularAllCanonicalBoundaryRetainedFinishIsNone
    allDirectBoundaryDeferredRetainedFinishIsNone runDirectResolvedObserve
  apply evalDist_bind_congr
  intro rootOption hroot
  cases rootOption with
  | none => rfl
  | some result =>
      have hcore := resolvedCore_of_mem_runDirectResolvedFromTable
        (maskedPublishedTreeRoot.run emptySplitHashCache) emptyWitnessDeferredContext fuel table
        result DeferredContext.valid_empty.valuesConsistent (startTableAgrees_empty table) hroot
      have hraw := raw_done_of_mem_runDirectResolvedFromTable
        (maskedPublishedTreeRoot.run emptySplitHashCache) emptyWitnessDeferredContext fuel table
        result hroot
      have hpub := preservesPublishedValues_maskedPublishedTreeRoot
        LazyRevealProbe.State.empty emptySplitHashCache fuel result.context.state
        result.remaining result.value.1 result.value.2 publishedValues_empty hraw
      have hmat : ∀ coordinate, CoordinateMaterializedPublished coordinate result.context.state := by
        intro coordinate
        exact preservesCoordinateMaterializedPublished_maskedPublishedTreeRoot coordinate
          LazyRevealProbe.State.empty emptySplitHashCache fuel result.context.state
          result.remaining result.value.1 result.value.2
          (by simp [CoordinateMaterializedPublished, LazyRevealProbe.State.empty]) hraw
      have hcanonical := canonicalMaterializedValues_of_published table result.context hcore.2.2 hpub hmat
      simp only [finishObserve, canonicalizeObserve, hpub, ↓reduceIte, hcanonical.canonicalize_eq]
      exact evalDist_granularRetainedRestObserve_eq_allDirect adversary parameter table ftsSecret
        result.context result.remaining result.value hcore.2.1 hcore.2.2 hpub hcanonical

theorem evalDist_sampledCanonicalBoundary_eq_deferred
    (adversary : Adversary) (parameter : PublicParameter)
    (ftsSecret : Index → FtsTree → FtsLeaf → Digest) (fuel : Nat) :
    evalDist (sampledGranularAllCanonicalBoundaryRetainedFinishIsNone adversary parameter ftsSecret fuel) =
      evalDist (sampledCanonicalDeferredFinishIsNone adversary parameter ftsSecret fuel) := by
  rw [evalDist_sampledCanonicalDeferredFinishIsNone_eq_allDirect]
  unfold sampledGranularAllCanonicalBoundaryRetainedFinishIsNone sampledAllDirectBoundaryFinishIsNone
  apply OracleComp.DeferredSampling.evalDist_bind_congr_left
  intro table
  exact evalDist_granularAllCanonicalBoundaryRetainedFinishIsNone_eq_allDirect
    adversary parameter table ftsSecret fuel

theorem probEvent_sampledActualRetained_verifyProbe_le_thirteen_mul
    (adversary : Adversary) (parameter : PublicParameter)
    (ftsSecret : Index → FtsTree → FtsLeaf → Digest) (q : Nat)
    (hexpanded : ∀ table root,
      (simulateQ
        (SphincsSecurity.expandedAdversaryImpl
          (⟨parameter, root, tableOtsSecret (extendStartTable table), ftsSecret⟩ : SecretKey))
        (retainedGameRestComputation adversary ⟨root, parameter⟩)).IsQueryBoundP
          (fun query => query matches Sum.inr _) q)
    (hq : q ≤ 2 ^ securityBits) :
    Pr[fun result => WinningRetainedVerifyProbeWitness parameter
        (extendStartTable result.1) ftsSecret result.2 |
      sampledActualRetainedOtsHashTable adversary parameter ftsSecret] ≤
        ((13 * q : Nat) : ENNReal) * ((2 ^ digestBits : Nat) : ENNReal)⁻¹ := by
  apply (probEvent_sampledActualRetainedOtsHashTable_verifyProbe_le_canonicalDeferred
    adversary parameter ftsSecret q).trans
  rw [← OracleComp.probOutput_congr (show true = true from rfl)
    (evalDist_sampledCanonicalBoundary_eq_deferred adversary parameter ftsSecret q)]
  exact probEvent_sampledCanonicalBoundary_finishIsNone_le_thirteen_mul
    adversary parameter ftsSecret q hexpanded hq

theorem security_of_completed_canonical_boundary : SphincsSecurityStatement := by
  apply security_of_sampledWinningRetainedVerifyProbe_grouped_le_mul 13 (by omega)
  intro q _hqPos adversary hq hqMax parameter hparameter ftsSecret hfts
  exact probEvent_sampledActualRetained_verifyProbe_le_thirteen_mul adversary parameter ftsSecret q
    (fun table root => isQueryBoundP_expandedRetained_all_tables_roots adversary q hq
      parameter hparameter table ftsSecret hfts root) hqMax

end SphincsSecurity.Concrete.OtsProbeSimulation
