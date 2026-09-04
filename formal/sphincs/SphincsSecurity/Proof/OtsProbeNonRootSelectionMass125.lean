import SphincsSecurity.Proof.OtsProbeRootSelectionMass125

namespace SphincsSecurity.Concrete.OtsProbeSimulation

open OracleComp OracleSpec ENNReal

attribute [local irreducible] maskedPublishedTreeRoot

/-- Every selected non-root candidate still has an unexposed output at selection time. -/
def PrivateOrdinalSelectionFresh : Option PrivateOrdinalSelection → Prop
  | none => True
  | some selection => selection.candidate.HasStructuralParent ∧
      CandidatePositionsFreshExceptLayerRoots selection.context

theorem privateOrdinalSelectionFresh_of_mem_finish
    (table : OtsSecretIndex → HashOutput)
    (observe : DeferredContext → Nat → α → List Probe →
      ProbComp (Option PrivateOrdinalSelection))
    (candidates : List Probe) (result : DirectWitnessResult α)
    (output : Option PrivateOrdinalSelection)
    (houtput : output ∈ support
      (finishDirectPrivateOrdinalSelection
        (canonicalizeDirectPrivateOrdinalSelection table observe) candidates result))
    (hobserve : ∀ resolved,
      result = .done resolved → PublishedValues resolved.context.state →
      ∀ selected, selected ∈ support
        (observe (canonicalizeMaterializedValues table resolved.context)
          resolved.remaining resolved.value candidates) →
        PrivateOrdinalSelectionFresh selected) :
    PrivateOrdinalSelectionFresh output := by
  classical
  cases result with
  | stoppedFuel =>
      simp [finishDirectPrivateOrdinalSelection] at houtput
      subst output
      trivial
  | stoppedOrdinary =>
      simp [finishDirectPrivateOrdinalSelection] at houtput
      subst output
      trivial
  | stoppedPrivate witness =>
      simp [finishDirectPrivateOrdinalSelection] at houtput
      subst output
      trivial
  | done resolved =>
      change output ∈ support (canonicalizeDirectPrivateOrdinalSelection table observe
        resolved.context resolved.remaining resolved.value candidates) at houtput
      unfold canonicalizeDirectPrivateOrdinalSelection at houtput
      by_cases hprivate : PrivateStructuralHit
          (canonicalizeMaterializedValues table resolved.context)
      · simp [hprivate] at houtput
        subst output
        trivial
      · simp only [hprivate, ↓reduceIte] at houtput
        by_cases hpublished : PublishedValues resolved.context.state
        · simp only [hpublished, ↓reduceIte] at houtput
          by_cases hcomplete : DeferredCompletable table
              (canonicalizeMaterializedValues table resolved.context)
          · simp only [hcomplete, ↓reduceIte] at houtput
            exact hobserve resolved rfl hpublished output houtput
          · simp [hcomplete] at houtput
            subst output
            trivial
        · simp [hpublished] at houtput
          subst output
          trivial

set_option maxRecDepth 100000 in
theorem privateOrdinalSelectionFresh_of_mem_direct
    (ordinal : Nat) (parameter : PublicParameter) (root : Digest)
    (ftsSecret : Index → FtsTree → FtsLeaf → Digest)
    (computation : OracleComp (OracleWorld + SigningSpec) α)
    (candidates : List Probe) (context : DeferredContext) (fuel : Nat)
    (table : OtsSecretIndex → HashOutput) (cache : SplitHashCache)
    (hparents : CandidatesHaveStructuralParent candidates)
    (hfresh : CandidatePositionsFreshExceptLayerRoots context)
    (hpublishedContext : PublishedValues context.state)
    (output : Option PrivateOrdinalSelection)
    (houtput : output ∈ support
      (directDetailedBoundaryPrivateOrdinalSelection ordinal parameter root ftsSecret computation
        candidates context fuel table cache)) :
    PrivateOrdinalSelectionFresh output := by
  induction computation using OracleComp.inductionOn generalizing
      candidates context fuel cache output with
  | pure value =>
      rw [directDetailedBoundaryPrivateOrdinalSelection, OracleComp.construct_pure] at houtput
      simp only [support_pure, Set.mem_singleton_iff] at houtput
      subst output
      unfold selectedPrivateOrdinal?
      split
      · exact ⟨candidateHasStructuralParent_get hparents _ _, hfresh⟩
      · trivial
  | query_bind query next ih =>
      rw [directDetailedBoundaryPrivateOrdinalSelection,
        OracleComp.construct_query_bind] at houtput
      by_cases hselected : ordinal < candidates.length
      · simp only [hselected, ↓reduceDIte, support_pure, Set.mem_singleton_iff] at houtput
        subst output
        exact ⟨candidateHasStructuralParent_get hparents _ _, hfresh⟩
      · simp only [hselected, ↓reduceDIte] at houtput
        cases query with
        | inl worldQuery =>
            cases worldQuery with
            | inl n =>
                rw [mem_support_bind_iff] at houtput
                obtain ⟨result, hresult, hfinish⟩ := houtput
                apply privateOrdinalSelectionFresh_of_mem_finish table _ candidates result
                  output hfinish
                intro resolved heq hpublished selected hselected
                subst result
                exact ih resolved.value.1 candidates
                  (canonicalizeMaterializedValues table resolved.context) resolved.remaining
                  resolved.value.2 hparents
                  (candidatePositionsFreshExceptLayerRoots_uniformStep n context fuel table cache
                    resolved hfresh hresult)
                  hpublished.to_canonicalizedMaterializedValues selected hselected
            | inr input =>
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
                        (rootAwarePlannedCandidate? parameter input context.state)).length :=
                    hnextSelected
                  simp only [hactual, ↓reduceDIte, support_pure,
                    Set.mem_singleton_iff] at houtput
                  subst output
                  exact ⟨candidateHasStructuralParent_get hnextParents _ _, hfresh⟩
                · have hactual : ¬ordinal <
                      (appendPlannedCandidate candidates
                        (rootAwarePlannedCandidate? parameter input context.state)).length :=
                    hnextSelected
                  simp only [hactual, ↓reduceDIte] at houtput
                  rw [mem_support_bind_iff] at houtput
                  obtain ⟨result, hresult, hfinish⟩ := houtput
                  apply privateOrdinalSelectionFresh_of_mem_finish table _ nextCandidates result
                    output hfinish
                  intro resolved heq hpublished selected hselected
                  subst result
                  exact ih resolved.value.1 nextCandidates
                    (canonicalizeMaterializedValues table resolved.context) resolved.remaining
                    resolved.value.2 hnextParents
                    (candidatePositionsFreshExceptLayerRoots_hashStep parameter input plan context
                      fuel table cache resolved hfresh hpublishedContext hresult)
                    hpublished.to_canonicalizedMaterializedValues selected hselected
        | inr message =>
            rw [mem_support_bind_iff] at houtput
            obtain ⟨result, hresult, hfinish⟩ := houtput
            apply privateOrdinalSelectionFresh_of_mem_finish table _ candidates result
              output hfinish
            intro resolved heq hpublished selected hselected
            subst result
            exact ih resolved.value.1 candidates
              (canonicalizeMaterializedValues table resolved.context) resolved.remaining
              resolved.value.2 hparents
              (candidatePositionsFreshExceptLayerRoots_signStep parameter root ftsSecret message
                context fuel table cache resolved hfresh hpublishedContext hresult)
              hpublished.to_canonicalizedMaterializedValues selected hselected

set_option maxRecDepth 100000 in
theorem privateOrdinalSelectionFresh_of_mem_granularAllCanonical
    (ordinal : Nat) (adversary : Adversary) (parameter : PublicParameter)
    (table : OtsSecretIndex → HashOutput)
    (ftsSecret : Index → FtsTree → FtsLeaf → Digest) (fuel : Nat)
    (output : Option PrivateOrdinalSelection)
    (houtput : output ∈ support
      (granularAllCanonicalPrivateOrdinalSelection ordinal adversary parameter table ftsSecret
        fuel)) :
    PrivateOrdinalSelectionFresh output := by
  unfold granularAllCanonicalPrivateOrdinalSelection at houtput
  rw [mem_support_bind_iff] at houtput
  obtain ⟨result, hresult, hfinish⟩ := houtput
  apply privateOrdinalSelectionFresh_of_mem_finish table _ [] result output hfinish
  intro resolved heq hpublished selected hselected
  subst result
  exact privateOrdinalSelectionFresh_of_mem_direct ordinal parameter resolved.value.1 ftsSecret
    (retainedGameRestComputation adversary ⟨resolved.value.1, parameter⟩) []
    (canonicalizeMaterializedValues table resolved.context) resolved.remaining table
    resolved.value.2 candidatesHaveStructuralParent_nil
    (candidatePositionsFreshExceptLayerRoots_of_done_maskedPublishedTreeRoot fuel table resolved
      hresult) hpublished.to_canonicalizedMaterializedValues selected hselected

def PrivateOrdinalSelectionNonRoot : Option PrivateOrdinalSelection → Prop
  | none => False
  | some selection => ¬selection.candidate.IsLayerRoot

theorem probEvent_selectionNonRootFire_le_selected_mass
    (selection : ProbComp (Option PrivateOrdinalSelection))
    (hfresh : ∀ output ∈ support selection, PrivateOrdinalSelectionFresh output) :
    Pr[fun hit => hit = true | selection >>= privateOrdinalSelectionNonRootFire] ≤
      Pr[PrivateOrdinalSelectionNonRoot | selection] *
        ((2 ^ digestBits : Nat) : ENNReal)⁻¹ := by
  classical
  rw [probEvent_bind_eq_tsum, probEvent_eq_tsum_ite, ← ENNReal.tsum_mul_right]
  apply ENNReal.tsum_le_tsum
  intro output
  by_cases hsupport : output ∈ support selection
  · have hvalid := hfresh output hsupport
    cases output with
    | none => simp [privateOrdinalSelectionNonRootFire, PrivateOrdinalSelectionNonRoot]
    | some selected =>
        by_cases hroot : selected.candidate.IsLayerRoot
        · simp [PrivateOrdinalSelectionNonRoot, privateOrdinalSelectionNonRootFire,
            nonRootHiddenPrivateCandidateFire, hroot]
        · simp only [PrivateOrdinalSelectionNonRoot, hroot, not_false_eq_true, if_true]
          apply mul_le_mul' le_rfl
          exact probEvent_nonRootHiddenPrivateCandidateFire_le selected.candidate selected.context
            hvalid.1 hvalid.2
  · simp [probOutput_eq_zero_of_not_mem_support hsupport]

set_option maxRecDepth 100000 in
theorem probEvent_granularNonRootRisk_le_selected_mass
    (ordinal : Nat) (adversary : Adversary) (parameter : PublicParameter)
    (table : OtsSecretIndex → HashOutput)
    (ftsSecret : Index → FtsTree → FtsLeaf → Digest) (fuel : Nat) :
    Pr[fun hit => hit = true |
        granularAllCanonicalPrivateOrdinalNonRootRisk ordinal adversary parameter table ftsSecret
          fuel] ≤
      Pr[PrivateOrdinalSelectionNonRoot |
        granularAllCanonicalPrivateOrdinalSelection ordinal adversary parameter table ftsSecret
          fuel] * ((2 ^ digestBits : Nat) : ENNReal)⁻¹ := by
  rw [← granularAllCanonicalPrivateOrdinalSelection_bind_nonRootFire]
  apply probEvent_selectionNonRootFire_le_selected_mass
  exact privateOrdinalSelectionFresh_of_mem_granularAllCanonical ordinal adversary parameter
    table ftsSecret fuel

end SphincsSecurity.Concrete.OtsProbeSimulation
