import SphincsSecurity.Proof.OtsProbeResolvedBoundaryPrivateWitnessOrdinalHiddenFreshSigner

/-!
# Non-root ordinal risk

The least selected ordinal is split by whether its candidate names a layer root. This risk is the
existing hidden prefix risk with root candidates gated to false. The weakened freshness invariant
is therefore sufficient through the concrete signer.
-/

namespace SphincsSecurity.Concrete.OtsProbeSimulation

open OracleComp OracleSpec ENNReal

attribute [local instance] Classical.propDecidable

noncomputable def nonRootHiddenPrivateCandidateFire
    (candidate : Probe) (context : DeferredContext) : ProbComp Bool :=
  if candidate.IsLayerRoot then pure false else hiddenPrivateCandidateFire candidate context

theorem probEvent_nonRootHiddenPrivateCandidateFire_le
    (candidate : Probe) (context : DeferredContext)
    (hparent : candidate.HasStructuralParent)
    (hfresh : CandidatePositionsFreshExceptLayerRoots context) :
    Pr[fun hit : Bool => hit = true |
        nonRootHiddenPrivateCandidateFire candidate context] ≤
      ((2 ^ digestBits : Nat) : ℝ≥0∞)⁻¹ := by
  by_cases hroot : candidate.IsLayerRoot
  · simp [nonRootHiddenPrivateCandidateFire, hroot]
  · rw [nonRootHiddenPrivateCandidateFire, if_neg hroot]
    rw [probEvent_eq_eq_probOutput]
    exact probEvent_hiddenPrivateCandidateFire_le_of_freshExceptLayerRoots candidate context
      hparent hroot hfresh

noncomputable def directDetailedBoundaryPrivateOrdinalNonRootRisk
    (ordinal : Nat) (parameter : PublicParameter) (root : Digest)
    (ftsSecret : Index → FtsTree → FtsLeaf → Digest)
    (computation : OracleComp (OracleWorld + SigningSpec) α)
    (candidates : List Probe) (context : DeferredContext) (fuel : Nat)
    (table : OtsSecretIndex → HashOutput) (cache : SplitHashCache) : ProbComp Bool := by
  classical
  exact OracleComp.construct
    (C := fun _ : OracleComp (OracleWorld + SigningSpec) α =>
      List Probe → DeferredContext → Nat → (OtsSecretIndex → HashOutput) →
        SplitHashCache → ProbComp Bool)
    (fun _value candidates context _fuel _table _cache =>
      if hselected : ordinal < candidates.length then
        nonRootHiddenPrivateCandidateFire (candidates.get ⟨ordinal, hselected⟩) context
      else pure false)
    (fun query _next recursivelyRun candidates context fuel table cache =>
      if hselected : ordinal < candidates.length then
        nonRootHiddenPrivateCandidateFire (candidates.get ⟨ordinal, hselected⟩) context
      else
        match query with
        | .inl (.inl n) =>
            runDirectResolvedWitnessFromTable context fuel table ((splitUniformImpl n).run cache) >>=
              finishDirectWitnessOrdinalRisk
                (canonicalizeDirectWitnessOrdinalRisk table
                  (fun nextContext remaining value laterCandidates =>
                    recursivelyRun value.1 laterCandidates nextContext remaining table value.2))
                candidates
        | .inl (.inr input) =>
            let plan := purePlanProbingHashQuery parameter input context.state
            let nextCandidates := appendPlannedCandidate candidates
              (rootAwarePlannedCandidate? parameter input context.state)
            if hnextSelected : ordinal < nextCandidates.length then
              nonRootHiddenPrivateCandidateFire
                (nextCandidates.get ⟨ordinal, hnextSelected⟩) context
            else
              runDirectResolvedWitnessFromTable context fuel table
                  ((probingHashQueryAfterPlan parameter input plan).run cache) >>=
                finishDirectWitnessOrdinalRisk
                  (canonicalizeDirectWitnessOrdinalRisk table
                    (fun nextContext remaining value laterCandidates =>
                      recursivelyRun value.1 laterCandidates nextContext remaining table value.2))
                  nextCandidates
        | .inr message =>
            runDirectResolvedWitnessFromTable context fuel table
                ((maskedSign parameter root ftsSecret message).run cache) >>=
              finishDirectWitnessOrdinalRisk
                (canonicalizeDirectWitnessOrdinalRisk table
                  (fun nextContext remaining value laterCandidates =>
                    recursivelyRun value.1 laterCandidates nextContext remaining table value.2))
                candidates)
    computation candidates context fuel table cache

theorem directDetailedBoundaryPrivateOrdinalNonRootRisk_eq_fire_of_selected
    (ordinal : Nat) (parameter : PublicParameter) (root : Digest)
    (ftsSecret : Index → FtsTree → FtsLeaf → Digest)
    (computation : OracleComp (OracleWorld + SigningSpec) α)
    (candidates : List Probe) (context : DeferredContext) (fuel : Nat)
    (table : OtsSecretIndex → HashOutput) (cache : SplitHashCache)
    (hselected : ordinal < candidates.length) :
    directDetailedBoundaryPrivateOrdinalNonRootRisk ordinal parameter root ftsSecret computation
        candidates context fuel table cache =
      nonRootHiddenPrivateCandidateFire
        (candidates.get ⟨ordinal, hselected⟩) context := by
  induction computation using OracleComp.inductionOn generalizing candidates context fuel cache with
  | pure value =>
      rw [directDetailedBoundaryPrivateOrdinalNonRootRisk, OracleComp.construct_pure]
      simp only [hselected, ↓reduceDIte]
  | query_bind query next ih =>
      rw [directDetailedBoundaryPrivateOrdinalNonRootRisk, OracleComp.construct_query_bind]
      simp only [hselected, ↓reduceDIte]

set_option maxHeartbeats 2000000 in
set_option maxRecDepth 100000 in
theorem probEvent_directDetailedBoundaryPrivateOrdinalNonRootRisk_le
    (ordinal : Nat) (parameter : PublicParameter) (root : Digest)
    (ftsSecret : Index → FtsTree → FtsLeaf → Digest)
    (computation : OracleComp (OracleWorld + SigningSpec) α)
    (candidates : List Probe) (context : DeferredContext) (fuel : Nat)
    (table : OtsSecretIndex → HashOutput) (cache : SplitHashCache)
    (hparents : CandidatesHaveStructuralParent candidates)
    (hfresh : CandidatePositionsFreshExceptLayerRoots context)
    (hpublishedContext : PublishedValues context.state) :
    Pr[fun hit : Bool => hit = true |
        directDetailedBoundaryPrivateOrdinalNonRootRisk ordinal parameter root ftsSecret
          computation candidates context fuel table cache] ≤
      ((2 ^ digestBits : Nat) : ℝ≥0∞)⁻¹ := by
  induction computation using OracleComp.inductionOn generalizing candidates context fuel cache with
  | pure value =>
      rw [directDetailedBoundaryPrivateOrdinalNonRootRisk, OracleComp.construct_pure]
      by_cases hselected : ordinal < candidates.length
      · simp only [hselected, ↓reduceDIte]
        exact probEvent_nonRootHiddenPrivateCandidateFire_le
          (candidates.get ⟨ordinal, hselected⟩) context
          (candidateHasStructuralParent_get hparents ordinal hselected) hfresh
      · simp [hselected]
  | query_bind query next ih =>
      cases query with
      | inl worldQuery =>
          cases worldQuery with
          | inl n =>
              rw [directDetailedBoundaryPrivateOrdinalNonRootRisk,
                OracleComp.construct_query_bind]
              by_cases hselected : ordinal < candidates.length
              · simp only [hselected, ↓reduceDIte]
                exact probEvent_nonRootHiddenPrivateCandidateFire_le
                  (candidates.get ⟨ordinal, hselected⟩) context
                  (candidateHasStructuralParent_get hparents ordinal hselected) hfresh
              · simp only [hselected, ↓reduceDIte]
                apply probEvent_bind_le_of_forall_le
                intro result hresult
                apply probEvent_finishDirectWitnessOrdinalRisk_le table _ candidates result _
                intro resolved heq hpublished hcompletable
                subst result
                exact ih resolved.value.1 candidates
                  (canonicalizeMaterializedValues table resolved.context) resolved.remaining
                  resolved.value.2 hparents
                  (candidatePositionsFreshExceptLayerRoots_uniformStep n context fuel table cache
                    resolved hfresh hresult)
                  hpublished.to_canonicalizedMaterializedValues
          | inr input =>
              rw [directDetailedBoundaryPrivateOrdinalNonRootRisk,
                OracleComp.construct_query_bind]
              by_cases hselected : ordinal < candidates.length
              · simp only [hselected, ↓reduceDIte]
                exact probEvent_nonRootHiddenPrivateCandidateFire_le
                  (candidates.get ⟨ordinal, hselected⟩) context
                  (candidateHasStructuralParent_get hparents ordinal hselected) hfresh
              · simp only [hselected, ↓reduceDIte]
                let plan := purePlanProbingHashQuery parameter input context.state
                let nextCandidates := appendPlannedCandidate candidates
                  (rootAwarePlannedCandidate? parameter input context.state)
                have hnextParents : CandidatesHaveStructuralParent nextCandidates := by
                  apply hparents.appendPlanned
                    (rootAwarePlannedCandidate? parameter input context.state)
                  intro candidate hcandidate
                  exact rootAwarePlannedCandidate?_hasStructuralParent hcandidate
                by_cases hnextSelected : ordinal < nextCandidates.length
                · have hactual : ordinal <
                      (appendPlannedCandidate candidates
                        (rootAwarePlannedCandidate? parameter input context.state)).length := by
                    simpa [nextCandidates, plan] using hnextSelected
                  rw [dif_pos hactual]
                  simpa [nextCandidates, plan] using
                    (probEvent_nonRootHiddenPrivateCandidateFire_le
                      (nextCandidates.get ⟨ordinal, hnextSelected⟩) context
                      (candidateHasStructuralParent_get hnextParents ordinal hnextSelected) hfresh)
                · have hactual : ¬ordinal <
                      (appendPlannedCandidate candidates
                        (rootAwarePlannedCandidate? parameter input context.state)).length := by
                    simpa [nextCandidates, plan] using hnextSelected
                  rw [dif_neg hactual]
                  apply probEvent_bind_le_of_forall_le
                  intro result hresult
                  apply probEvent_finishDirectWitnessOrdinalRisk_le table _ nextCandidates result _
                  intro resolved heq hpublished hcompletable
                  subst result
                  exact ih resolved.value.1 nextCandidates
                    (canonicalizeMaterializedValues table resolved.context) resolved.remaining
                    resolved.value.2 hnextParents
                    (candidatePositionsFreshExceptLayerRoots_hashStep parameter input plan context
                      fuel table cache resolved hfresh hpublishedContext hresult)
                    hpublished.to_canonicalizedMaterializedValues
      | inr message =>
          rw [directDetailedBoundaryPrivateOrdinalNonRootRisk,
            OracleComp.construct_query_bind]
          by_cases hselected : ordinal < candidates.length
          · simp only [hselected, ↓reduceDIte]
            exact probEvent_nonRootHiddenPrivateCandidateFire_le
              (candidates.get ⟨ordinal, hselected⟩) context
              (candidateHasStructuralParent_get hparents ordinal hselected) hfresh
          · simp only [hselected, ↓reduceDIte]
            apply probEvent_bind_le_of_forall_le
            intro result hresult
            apply probEvent_finishDirectWitnessOrdinalRisk_le table _ candidates result _
            intro resolved heq hpublished hcompletable
            subst result
            exact ih resolved.value.1 candidates
              (canonicalizeMaterializedValues table resolved.context) resolved.remaining
              resolved.value.2 hparents
              (candidatePositionsFreshExceptLayerRoots_signStep parameter root ftsSecret message
                context fuel table cache resolved hfresh hpublishedContext hresult)
              hpublished.to_canonicalizedMaterializedValues

end SphincsSecurity.Concrete.OtsProbeSimulation
