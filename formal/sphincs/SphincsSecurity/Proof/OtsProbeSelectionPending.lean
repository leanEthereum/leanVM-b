import SphincsSecurity.Proof.OtsProbeSelectionHistory

namespace SphincsSecurity.Concrete.OtsProbeSimulation

open OracleComp OracleSpec ENNReal

attribute [local irreducible] maskedPublishedTreeRoot

set_option maxRecDepth 100000

theorem pendingCoveredBy_of_mem_runPermissiveFromTable
    (candidates : List Probe) (computation : OracleComp (LazyRevealProbe.World Coordinate) α)
    (state : LazyRevealProbe.State Coordinate) (fuel : Nat)
    (table : OtsSecretIndex → HashOutput) (result : CleanRunResult α)
    (hcovered : PendingCoveredBy candidates (directDeferredContext state))
    (hbound : computation.IsQueryBoundP (IsUncoveredProbe candidates) 0)
    (hresult : some result ∈ support (runPermissiveFromTable state fuel table computation)) :
    PendingCoveredBy candidates (directDeferredContext result.state) := by
  induction computation using OracleComp.inductionOn generalizing state fuel with
  | pure value =>
      simp [runPermissiveFromTable] at hresult
      rcases hresult with ⟨rfl, rfl, rfl, rfl⟩
      exact hcovered
  | query_bind input next ih =>
      rw [OracleComp.isQueryBoundP_query_bind_iff] at hbound
      cases input with
      | uniform n =>
          rw [runPermissiveFromTable_uniform_query_bind, mem_support_bind_iff] at hresult
          obtain ⟨output, _houtput, htail⟩ := hresult
          exact ih output state fuel hcovered (hbound.2 output) htail
      | hashOutput =>
          rw [runPermissiveFromTable_hashOutput_query_bind, mem_support_bind_iff] at hresult
          obtain ⟨output, _houtput, htail⟩ := hresult
          exact ih output state fuel hcovered (hbound.2 output) htail
      | ensure coordinate =>
          rw [runPermissiveFromTable_ensure_query_bind] at hresult
          exact ih () (state.ensure coordinate) fuel hcovered (hbound.2 ()) hresult
      | probe coordinate digest =>
          have hmem : (⟨coordinate, digest⟩ : Probe) ∈ candidates := by
            simpa [IsUncoveredProbe] using hbound.1
          have htail : (next ()).IsQueryBoundP (IsUncoveredProbe candidates) 0 := by
            simpa [IsUncoveredProbe] using hbound.2 ()
          rw [runPermissiveFromTable_probe_query_bind] at hresult
          cases fuel with
          | zero => simp at hresult
          | succ remaining =>
              by_cases hrevealed : coordinate ∈ state.revealed
              · simp only [hrevealed, ↓reduceIte] at hresult
                exact ih () state remaining hcovered htail hresult
              · simp only [hrevealed, ↓reduceIte] at hresult
                exact ih () (state.addPending coordinate digest) remaining
                  (hcovered.addPending_of_mem ⟨coordinate, digest⟩ hmem) htail hresult
      | peek coordinate =>
          rw [runPermissiveFromTable_peek_query_bind] at hresult
          exact ih (state.values coordinate) state fuel hcovered (hbound.2 _) hresult
      | publish coordinate =>
          rw [runPermissiveFromTable_publish_query_bind] at hresult
          exact ih () (state.publish coordinate) fuel hcovered (hbound.2 ()) hresult
      | reveal coordinate =>
          rw [runPermissiveFromTable_reveal_query_bind] at hresult
          cases hstate : state.values coordinate with
          | some output =>
              simp only [hstate] at hresult
              exact ih output state fuel hcovered (hbound.2 output) hresult
          | none =>
              simp only [hstate] at hresult
              cases coordinate with
              | chainStart lay tree leafIdx chainIdx =>
                  exact ih _ (state.materialize (.chainStart lay tree leafIdx chainIdx)
                    (table ⟨lay, tree, leafIdx, chainIdx⟩)) fuel
                    (hcovered.clearPending _) (hbound.2 _) hresult
              | position position =>
                  rw [mem_support_bind_iff] at hresult
                  obtain ⟨output, _houtput, htail⟩ := hresult
                  exact ih output (state.materialize (.position position) output) fuel
                    (hcovered.clearPending _) (hbound.2 output) htail

theorem probingHashQueryAfterPublicPlan_uncoveredProbeBound
    (parameter : PublicParameter) (input : HashInput) (publicState : LazyRevealProbe.State Coordinate)
    (plan : PlannedHashQuery) (candidates : List Probe)
    (hplanned : ∀ candidate, plan.candidate? = some candidate → candidate ∈ candidates)
    (cache : SplitHashCache) :
    ((probingHashQueryAfterPublicPlan parameter input publicState plan).run cache).IsQueryBoundP
      (IsUncoveredProbe candidates) 0 := by
  unfold probingHashQueryAfterPublicPlan
  rw [StateT.run_bind]
  apply OracleComp.isQueryBoundP_bind (n := 0) (m := 0)
  · cases hopt : plan.candidate? with
    | none => simp [executeCandidate?]
    | some candidate =>
        have hmem := hplanned candidate hopt
        change (LazyRevealProbe.probeQuery candidate.coordinate candidate.candidate).IsQueryBoundP
          (IsUncoveredProbe candidates) 0
        unfold LazyRevealProbe.probeQuery
        rw [OracleComp.isQueryBoundP_query_iff]
        simp [IsUncoveredProbe, hmem]
  · intro result _hresult
    exact OracleComp.IsQueryBoundP.of_imp (isUncoveredProbe_imp_isProbe candidates)
      (probingHashQueryPublicAction_probeFree parameter input publicState plan.action result.2)

theorem pendingCoveredBy_of_mem_delayedPermissiveDetailedOrdinalSelection
    (ordinal : Nat) (parameter : PublicParameter) (root : Digest)
    (ftsSecret : Index → FtsTree → FtsLeaf → Digest)
    (computation : OracleComp (OracleWorld + SigningSpec) α)
    (candidates : List Probe) (state : LazyRevealProbe.State Coordinate) (fuel : Nat)
    (table : OtsSecretIndex → HashOutput) (cache : SplitHashCache)
    (hcovered : PendingCoveredBy candidates (directDeferredContext state))
    (hlength : candidates.length ≤ ordinal) (selection : PermissivePrivateOrdinalSelection)
    (hselection : some selection ∈ support
      (delayedPermissiveDetailedOrdinalSelection ordinal parameter root ftsSecret computation
        candidates state fuel table cache)) :
    PendingCoveredBy (selection.candidates.take ordinal) (directDeferredContext selection.state) := by
  induction computation using OracleComp.inductionOn generalizing candidates state fuel cache with
  | pure value =>
      rw [delayedPermissiveDetailedOrdinalSelection, OracleComp.construct_pure] at hselection
      have hnotSelected : ¬ordinal < candidates.length := by omega
      simp [hnotSelected] at hselection
  | query_bind query next ih =>
      rw [delayedPermissiveDetailedOrdinalSelection, OracleComp.construct_query_bind] at hselection
      have hnotSelected : ¬ordinal < candidates.length := by omega
      simp only [hnotSelected, ↓reduceDIte] at hselection
      cases query with
      | inl worldQuery =>
          cases worldQuery with
          | inl n =>
              rw [mem_support_bind_iff] at hselection
              obtain ⟨result, hresult, hfinish⟩ := hselection
              cases result with
              | none => simp [finishPermissiveDetailedPrivateOrdinalSelection] at hfinish
              | some result =>
                  have hnextCovered := pendingCoveredBy_of_mem_runPermissiveFromTable
                    candidates ((splitUniformImpl n).run cache) state fuel table result hcovered
                    (OracleComp.IsQueryBoundP.of_imp (isUncoveredProbe_imp_isProbe candidates)
                      (splitUniformImpl_probeFree n cache)) hresult
                  exact ih result.value.1 candidates result.state result.remaining result.value.2
                    hnextCovered hlength hfinish
          | inr input =>
              let nextCandidates := permissiveRootAwareCandidates parameter input table state candidates
              by_cases hselected : ordinal < nextCandidates.length
              · have hactual : ordinal < (permissiveRootAwareCandidates parameter input table state candidates).length := hselected
                simp only [hactual, ↓reduceDIte, mem_support_pure_iff, Option.some.injEq] at hselection
                subst selection
                change PendingCoveredBy (nextCandidates.take ordinal) (directDeferredContext state)
                cases hcandidate : rootAwareCandidateForPlan? parameter input
                    (permissiveRootAwarePlan parameter input table state) with
                | none =>
                    have hnextEq : nextCandidates = candidates := by
                      simp [nextCandidates, permissiveRootAwareCandidates, appendPlannedCandidate, hcandidate]
                    rw [hnextEq] at hselected
                    omega
                | some candidate =>
                    have hlengthEq : candidates.length = ordinal := by
                      have hnextLength : nextCandidates.length = candidates.length + 1 := by
                        simp [nextCandidates, permissiveRootAwareCandidates, appendPlannedCandidate, hcandidate]
                      omega
                    have htake : nextCandidates.take ordinal = candidates := by
                      simp [nextCandidates, permissiveRootAwareCandidates, appendPlannedCandidate, hcandidate, hlengthEq]
                    rwa [htake]
              · have hactual : ¬ordinal < (permissiveRootAwareCandidates parameter input table state candidates).length := hselected
                simp only [hactual, ↓reduceDIte] at hselection
                rw [mem_support_bind_iff] at hselection
                obtain ⟨result, hresult, hfinish⟩ := hselection
                cases result with
                | none => simp [finishPermissiveDetailedPrivateOrdinalSelection] at hfinish
                | some result =>
                    have hnextCoveredAtStart : PendingCoveredBy nextCandidates (directDeferredContext state) := by
                      apply hcovered.mono_candidates
                      unfold nextCandidates permissiveRootAwareCandidates appendPlannedCandidate
                      cases rootAwareCandidateForPlan? parameter input
                        (permissiveRootAwarePlan parameter input table state) <;> simp
                    have hplanMem : ∀ candidate,
                        (permissiveRootAwarePlan parameter input table state).candidate? = some candidate →
                        candidate ∈ nextCandidates := by
                      intro candidate hcandidate
                      simp [nextCandidates, permissiveRootAwareCandidates, rootAwareCandidateForPlan?,
                        hcandidate, appendPlannedCandidate]
                    have hprobeBound := probingHashQueryAfterPublicPlan_uncoveredProbeBound
                      parameter input (materializedCanonicalContext table state).state
                      (permissiveRootAwarePlan parameter input table state) nextCandidates hplanMem cache
                    have hnextCovered := pendingCoveredBy_of_mem_runPermissiveFromTable
                      nextCandidates (delayedPermissivePublicAction parameter input table state cache)
                      state fuel table result hnextCoveredAtStart hprobeBound hresult
                    exact ih result.value.1 nextCandidates result.state result.remaining result.value.2
                      hnextCovered (by omega) hfinish
      | inr message =>
          rw [mem_support_bind_iff] at hselection
          obtain ⟨result, hresult, hfinish⟩ := hselection
          cases result with
          | none => simp [finishPermissiveDetailedPrivateOrdinalSelection] at hfinish
          | some result =>
              have hnextCovered := pendingCoveredBy_of_mem_runPermissiveFromTable
                candidates ((maskedSign parameter root ftsSecret message).run cache) state fuel table result hcovered
                (OracleComp.IsQueryBoundP.of_imp (isUncoveredProbe_imp_isProbe candidates)
                  (maskedSign_probeFree parameter root ftsSecret message cache)) hresult
              exact ih result.value.1 candidates result.state result.remaining result.value.2
                hnextCovered hlength hfinish

theorem pendingCoveredBy_of_mem_delayedSelectionExperiment
    (ordinal : Nat) (adversary : Adversary) (parameter : PublicParameter)
    (ftsSecret : Index → FtsTree → FtsLeaf → Digest) (fuel : Nat)
    (table : OtsSecretIndex → HashOutput) (selection : PermissivePrivateOrdinalSelection)
    (hselection : some selection ∈ support
      (delayedPermissiveDetailedSelectionExperimentAfterTable ordinal adversary parameter ftsSecret fuel table)) :
    PendingCoveredBy (selection.candidates.take ordinal) (directDeferredContext selection.state) := by
  unfold delayedPermissiveDetailedSelectionExperimentAfterTable at hselection
  rw [mem_support_bind_iff] at hselection
  obtain ⟨result, hresult, hselection⟩ := hselection
  cases result with
  | none => simp at hselection
  | some result =>
      have hpending := pending_eq_empty_of_mem_runCleanFromTable_maskedPublishedTreeRoot fuel table result hresult
      have hcovered : PendingCoveredBy [] (directDeferredContext result.state) := by
        intro entry hentry
        change entry ∈ result.state.pending at hentry
        simp [hpending] at hentry
      exact pendingCoveredBy_of_mem_delayedPermissiveDetailedOrdinalSelection ordinal parameter result.value.1 ftsSecret
        (retainedGameRestComputation adversary ⟨result.value.1, parameter⟩) [] result.state result.remaining
        result.table result.value.2 hcovered (Nat.zero_le _) selection hselection

theorem freshHiddenSelection_charges_of_mem_delayedSelectionExperiment
    (ordinal : Nat) (adversary : Adversary) (parameter : PublicParameter)
    (ftsSecret : Index → FtsTree → FtsLeaf → Digest) (fuel : Nat)
    (table : OtsSecretIndex → HashOutput) (selection : PermissivePrivateOrdinalSelection)
    (hselection : some selection ∈ support
      (delayedPermissiveDetailedSelectionExperimentAfterTable ordinal adversary parameter ftsSecret fuel table))
    (hfresh : FreshExistingHiddenSelection ordinal (some selection)) :
    unmaterializedCandidateCharge selection.state (some selection.candidate) = 0 ∧
      materializedCandidateCharge selection.state (some selection.candidate) = 1 := by
  refine ⟨unmaterializedCandidateCharge_eq_zero_of_existingHiddenHit selection.state selection.candidate hfresh.1, ?_⟩
  apply freshExistingHiddenSelection_materializedCharge_eq_one hfresh
  intro coordinate candidate hpending
  have hcovered := pendingCoveredBy_of_mem_delayedSelectionExperiment ordinal adversary parameter ftsSecret
    fuel table selection hselection
  obtain ⟨probe, hprobe, hcoordinate, hdigest⟩ := hcovered (coordinate, candidate) hpending
  have heq : probe = ⟨coordinate, candidate⟩ := by
    cases probe
    simp_all
  rwa [heq] at hprobe

end SphincsSecurity.Concrete.OtsProbeSimulation
