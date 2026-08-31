import SphincsSecurity.Proof.OtsProbeResolvedBoundaryPrivateWitnessOrdinalHiddenFresh

/-!
# One-unit hidden ordinal bound

The hidden ordinal risk costs one unit whenever every completed query step transports candidate
freshness across its canonical boundary. This file isolates that exact remaining interface from the
finite-union and witness machinery.
-/

namespace SphincsSecurity.Concrete.OtsProbeSimulation

open OracleComp OracleSpec ENNReal

attribute [local instance] Classical.propDecidable

def CandidatesHaveStructuralParent (candidates : List Probe) : Prop :=
  ∀ candidate ∈ candidates, candidate.HasStructuralParent

theorem candidatesHaveStructuralParent_nil :
    CandidatesHaveStructuralParent [] := by simp [CandidatesHaveStructuralParent]

theorem CandidatesHaveStructuralParent.appendCandidate
    {candidates : List Probe} (hparents : CandidatesHaveStructuralParent candidates)
    (candidate : Probe) (hparent : candidate.HasStructuralParent) :
    CandidatesHaveStructuralParent (candidates ++ [candidate]) := by
  intro other hmem
  rcases List.mem_append.mp hmem with hleft | hright
  · exact hparents other hleft
  · have heq : other = candidate := by simpa using hright
    subst other
    exact hparent

theorem CandidatesHaveStructuralParent.appendPlanned
    {candidates : List Probe} (hparents : CandidatesHaveStructuralParent candidates)
    (candidate? : Option Probe)
    (hcandidate : ∀ candidate, candidate? = some candidate →
      candidate.HasStructuralParent) :
    CandidatesHaveStructuralParent (appendPlannedCandidate candidates candidate?) := by
  cases hvalue : candidate? with
  | none => simpa [appendPlannedCandidate, hvalue] using hparents
  | some candidate =>
      exact hparents.appendCandidate candidate (hcandidate candidate hvalue)

theorem candidateHasStructuralParent_get
    {candidates : List Probe} (hparents : CandidatesHaveStructuralParent candidates)
    (ordinal : Nat) (hlt : ordinal < candidates.length) :
    (candidates.get ⟨ordinal, hlt⟩).HasStructuralParent :=
  hparents _ (List.get_mem candidates ⟨ordinal, hlt⟩)

theorem probEvent_finishDirectWitnessOrdinalRisk_le
    (table : OtsSecretIndex → HashOutput)
    (riskObserve : DeferredContext → Nat → α → List Probe → ProbComp Bool)
    (candidates : List Probe) (result : DirectWitnessResult α) (bound : ℝ≥0∞)
    (hcontinuation : ∀ resolved : ResolvedRunResult α,
      result = .done resolved →
      PublishedValues resolved.context.state →
      DeferredCompletable table (canonicalizeMaterializedValues table resolved.context) →
      Pr[fun hit : Bool => hit = true |
          riskObserve (canonicalizeMaterializedValues table resolved.context)
            resolved.remaining resolved.value candidates] ≤ bound) :
    Pr[fun hit : Bool => hit = true |
        finishDirectWitnessOrdinalRisk
          (canonicalizeDirectWitnessOrdinalRisk table riskObserve) candidates result] ≤
      bound := by
  cases result with
  | stoppedFuel => simp [finishDirectWitnessOrdinalRisk]
  | stoppedOrdinary => simp [finishDirectWitnessOrdinalRisk]
  | stoppedPrivate witness => simp [finishDirectWitnessOrdinalRisk]
  | done resolved =>
      unfold finishDirectWitnessOrdinalRisk canonicalizeDirectWitnessOrdinalRisk
      let canonical := canonicalizeMaterializedValues table resolved.context
      by_cases hhit : PrivateStructuralHit canonical
      · simp [canonical, hhit]
      · simp only [canonical, hhit]
        by_cases hpublished : PublishedValues resolved.context.state
        · simp only [hpublished, ↓reduceIte]
          by_cases hcompletable : DeferredCompletable table canonical
          · change DeferredCompletable table
                (canonicalizeMaterializedValues table resolved.context) at hcompletable
            rw [if_pos hcompletable]
            exact hcontinuation resolved rfl hpublished hcompletable
          · change ¬DeferredCompletable table
                (canonicalizeMaterializedValues table resolved.context) at hcompletable
            rw [if_neg hcompletable]
            simp
        · simp [hpublished]

set_option maxHeartbeats 2000000 in
set_option maxRecDepth 100000 in
theorem probEvent_directDetailedBoundaryPrivateOrdinalHiddenRisk_le
    (ordinal : Nat) (parameter : PublicParameter) (root : Digest)
    (ftsSecret : Index → FtsTree → FtsLeaf → Digest)
    (computation : OracleComp (OracleWorld + SigningSpec) α)
    (candidates : List Probe) (context : DeferredContext) (fuel : Nat)
    (table : OtsSecretIndex → HashOutput) (cache : SplitHashCache)
    (hparents : CandidatesHaveStructuralParent candidates)
    (hfresh : CandidatePositionsFresh context)
    (huniformFresh : ∀ n nextContext remaining nextCache result,
      CandidatePositionsFresh nextContext →
      DirectWitnessResult.done result ∈ support
        (runDirectResolvedWitnessFromTable nextContext remaining table
          ((splitUniformImpl n).run nextCache)) →
      PublishedValues result.context.state →
      CandidatePositionsFresh (canonicalizeMaterializedValues table result.context))
    (hhashFresh : ∀ input plan nextContext remaining nextCache result,
      CandidatePositionsFresh nextContext →
      DirectWitnessResult.done result ∈ support
        (runDirectResolvedWitnessFromTable nextContext remaining table
          ((probingHashQueryAfterPlan parameter input plan).run nextCache)) →
      PublishedValues result.context.state →
      CandidatePositionsFresh (canonicalizeMaterializedValues table result.context))
    (hsignFresh : ∀ message nextContext remaining nextCache result,
      CandidatePositionsFresh nextContext →
      DirectWitnessResult.done result ∈ support
        (runDirectResolvedWitnessFromTable nextContext remaining table
          ((maskedSign parameter root ftsSecret message).run nextCache)) →
      PublishedValues result.context.state →
      CandidatePositionsFresh (canonicalizeMaterializedValues table result.context)) :
    Pr[fun hit : Bool => hit = true |
        directDetailedBoundaryPrivateOrdinalHiddenRisk ordinal parameter root ftsSecret computation
          candidates context fuel table cache] ≤
      ((2 ^ digestBits : Nat) : ℝ≥0∞)⁻¹ := by
  induction computation using OracleComp.inductionOn generalizing candidates context fuel cache with
  | pure value =>
      rw [directDetailedBoundaryPrivateOrdinalHiddenRisk, OracleComp.construct_pure]
      by_cases hselected : ordinal < candidates.length
      · simp only [hselected, ↓reduceDIte]
        simpa using probEvent_hiddenPrivateCandidateFire_le_of_candidatePositionsFresh
          (candidates.get ⟨ordinal, hselected⟩) context
          (candidateHasStructuralParent_get hparents ordinal hselected) hfresh
      · simp [hselected]
  | query_bind query next ih =>
      cases query with
      | inl worldQuery =>
          cases worldQuery with
          | inl n =>
              rw [directDetailedBoundaryPrivateOrdinalHiddenRisk,
                OracleComp.construct_query_bind]
              by_cases hselected : ordinal < candidates.length
              · simp only [hselected, ↓reduceDIte]
                simpa using probEvent_hiddenPrivateCandidateFire_le_of_candidatePositionsFresh
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
                  (huniformFresh n context fuel cache resolved hfresh hresult hpublished)
          | inr input =>
              rw [directDetailedBoundaryPrivateOrdinalHiddenRisk,
                OracleComp.construct_query_bind]
              by_cases hselected : ordinal < candidates.length
              · simp only [hselected, ↓reduceDIte]
                simpa using probEvent_hiddenPrivateCandidateFire_le_of_candidatePositionsFresh
                  (candidates.get ⟨ordinal, hselected⟩) context
                  (candidateHasStructuralParent_get hparents ordinal hselected) hfresh
              · simp only [hselected, ↓reduceDIte]
                let plan := purePlanProbingHashQuery parameter input context.state
                let nextCandidates := appendPlannedCandidate candidates plan.candidate?
                have hnextParents : CandidatesHaveStructuralParent nextCandidates := by
                  apply hparents.appendPlanned plan.candidate?
                  intro candidate hcandidate
                  exact purePlanProbingHashQuery_candidate_hasStructuralParent parameter input
                    context.state candidate hcandidate
                by_cases hnextSelected : ordinal < nextCandidates.length
                · have hactual : ordinal <
                      (appendPlannedCandidate candidates
                        (purePlanProbingHashQuery parameter input context.state).candidate?).length := by
                    simpa [nextCandidates, plan] using hnextSelected
                  rw [dif_pos hactual]
                  simpa [nextCandidates, plan] using
                    (probEvent_hiddenPrivateCandidateFire_le_of_candidatePositionsFresh
                      (nextCandidates.get ⟨ordinal, hnextSelected⟩) context
                      (candidateHasStructuralParent_get hnextParents ordinal hnextSelected) hfresh)
                · have hactual : ¬ordinal <
                      (appendPlannedCandidate candidates
                        (purePlanProbingHashQuery parameter input context.state).candidate?).length := by
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
                    (hhashFresh input plan context fuel cache resolved hfresh hresult hpublished)
      | inr message =>
          rw [directDetailedBoundaryPrivateOrdinalHiddenRisk,
            OracleComp.construct_query_bind]
          by_cases hselected : ordinal < candidates.length
          · simp only [hselected, ↓reduceDIte]
            simpa using probEvent_hiddenPrivateCandidateFire_le_of_candidatePositionsFresh
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
              (hsignFresh message context fuel cache resolved hfresh hresult hpublished)

theorem probEvent_granularDetailedRetainedRestPrivateOrdinalHiddenRisk_le
    (adversary : Adversary) (parameter : PublicParameter)
    (table : OtsSecretIndex → HashOutput)
    (ftsSecret : Index → FtsTree → FtsLeaf → Digest)
    (ordinal : Nat) (context : DeferredContext) (fuel : Nat)
    (value : Digest × SplitHashCache) (candidates : List Probe)
    (hparents : CandidatesHaveStructuralParent candidates)
    (hfresh : CandidatePositionsFresh context)
    (huniformFresh : ∀ n nextContext remaining nextCache result,
      CandidatePositionsFresh nextContext →
      DirectWitnessResult.done result ∈ support
        (runDirectResolvedWitnessFromTable nextContext remaining table
          ((splitUniformImpl n).run nextCache)) →
      PublishedValues result.context.state →
      CandidatePositionsFresh (canonicalizeMaterializedValues table result.context))
    (hhashFresh : ∀ input plan nextContext remaining nextCache result,
      CandidatePositionsFresh nextContext →
      DirectWitnessResult.done result ∈ support
        (runDirectResolvedWitnessFromTable nextContext remaining table
          ((probingHashQueryAfterPlan parameter input plan).run nextCache)) →
      PublishedValues result.context.state →
      CandidatePositionsFresh (canonicalizeMaterializedValues table result.context))
    (hsignFresh : ∀ message nextContext remaining nextCache result,
      CandidatePositionsFresh nextContext →
      DirectWitnessResult.done result ∈ support
        (runDirectResolvedWitnessFromTable nextContext remaining table
          ((maskedSign parameter value.1 ftsSecret message).run nextCache)) →
      PublishedValues result.context.state →
      CandidatePositionsFresh (canonicalizeMaterializedValues table result.context)) :
    Pr[fun hit : Bool => hit = true |
        granularDetailedRetainedRestPrivateOrdinalHiddenRisk adversary parameter table ftsSecret
          ordinal context fuel value candidates] ≤
      ((2 ^ digestBits : Nat) : ℝ≥0∞)⁻¹ := by
  unfold granularDetailedRetainedRestPrivateOrdinalHiddenRisk
  exact probEvent_directDetailedBoundaryPrivateOrdinalHiddenRisk_le ordinal parameter value.1
    ftsSecret (retainedGameRestComputation adversary ⟨value.1, parameter⟩)
    candidates context fuel table value.2 hparents hfresh huniformFresh hhashFresh hsignFresh

end SphincsSecurity.Concrete.OtsProbeSimulation
